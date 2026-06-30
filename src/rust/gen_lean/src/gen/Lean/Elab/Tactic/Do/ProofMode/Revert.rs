// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Revert
// Imports: Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.Do.ProofMode.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_infer_type, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_mapFinIdxM_map___redArg,
    l_Array_reverse___redArg, l_Array_zip___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getNat, lean_name_append_index_after,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr6, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_Pi_instInhabited___redArg___lam__0, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::WFExtrinsicFix::l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_Core_mkFreshUserName,
    l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed,
    l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure,
    l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons, l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwError___redArg,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_consumeMData,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkAndN, l_Lean_mkApp3, l_Lean_mkApp7, l_Lean_mkApp8, l_Lean_mkAppN, l_Lean_mkAppRev,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAndIntroN, l_Lean_Meta_mkAndIntroN___boxed, l_Lean_Meta_mkEq,
    l_Lean_Meta_mkEq___boxed, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkEqRefl___boxed,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_inferType___boxed,
    l_Lean_Meta_instAddMessageContextMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateMVarsIfMVarApp___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLambdaFVars___boxed, l_Lean_Meta_withLocalDeclsDND___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value:
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
    m_data: [82, 101, 118, 101, 114, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value:
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
    m_data: [114, 101, 118, 101, 114, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 109, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__3_value
        ) as *mut leanh::LeanObject,
        9462318056131769598 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 109, 112, 111, 115, 115, 105, 98, 108, 101, 59, 32, 114, 101, 115, 46, 102, 111, 99,
        117, 115, 72, 121, 112, 32, 110, 111, 116, 32, 97, 32, 104, 121, 112, 111, 116, 104, 101,
        115, 105, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value:
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
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14_value:
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
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value:
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
    m_data: [115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__0_value
        ) as *mut leanh::LeanObject,
        5370976759840893899 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        97, 110, 100, 95, 112, 117, 114, 101, 95, 105, 110, 116, 114, 111, 95, 114, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,18104247681175793831 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,5435149840454673991 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__0_value) as *mut leanh::LeanObject,9146903220026413759 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__7_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__6_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0_value:
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
    m_fun: l_Lean_Meta_mkEqRefl___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value:
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
    m_fun: l_Lean_Meta_inferType___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
        109, 114, 101, 118, 101, 114, 116, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        32, 101, 120, 99, 101, 115, 115, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 105,
        110, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_value:
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
    m_data: [44, 32, 103, 111, 116, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        8738205681931236784 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,18104247681175793831 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,5435149840454673991 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject,6107604168496027576 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 114, 101, 118, 101, 114, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__2_value)
            as *mut leanh::LeanObject,
        12465766233631385938 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 114, 101, 118, 101, 114, 116, 80, 97, 116, 95, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__4_value)
            as *mut leanh::LeanObject,
        7862189086604081389 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 12,
    m_data: [
        109, 114, 101, 118, 101, 114, 116, 80, 97, 116, 226, 136, 128, 95, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__6_value)
            as *mut leanh::LeanObject,
        1021384599579944383 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__8_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10_value:
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
        78, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 77, 82, 101, 118, 101, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__1_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__2_value) as *mut leanh::LeanObject,17125385088244816172 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0(
    mut v___x_2801_: *mut leanh::LeanObject,
    mut v___x_2802_: *mut leanh::LeanObject,
    mut v___x_2803_: *mut leanh::LeanObject,
    mut v___x_2804_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2805_: *mut leanh::LeanObject,
    mut v_hyps_2806_: *mut leanh::LeanObject,
    mut v_restHyps_2807_: *mut leanh::LeanObject,
    mut v_focusHyp_2808_: *mut leanh::LeanObject,
    mut v_target_2809_: *mut leanh::LeanObject,
    mut v_proof_2810_: *mut leanh::LeanObject,
    mut v_toPure_2811_: *mut leanh::LeanObject,
    mut v_prf_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2813_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__0;
    v___x_2814_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__1;
    v___x_2815_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0___closed__2;
    v___x_2816_ = l_Lean_Name_mkStr6(
        v___x_2801_,
        v___x_2802_,
        v___x_2803_,
        v___x_2813_,
        v___x_2814_,
        v___x_2815_,
    );
    v___x_2817_ = l_Lean_mkConst(v___x_2816_, v___x_2804_);
    v_prf_2818_ = l_Lean_mkApp7(
        v___x_2817_,
        v_00_u03c3s_2805_,
        v_hyps_2806_,
        v_restHyps_2807_,
        v_focusHyp_2808_,
        v_target_2809_,
        v_proof_2810_,
        v_prf_2812_,
    );
    v___x_2819_ =
        leanh::lean_apply_2(v_toPure_2811_, leanh::lean_box(0), v_prf_2818_);
    return v___x_2819_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__5;
    v___x_2831_ = l_Lean_stringToMessageData(v___x_2830_);
    return v___x_2831_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1(
    mut v_goal_2832_: *mut leanh::LeanObject,
    mut v_toPure_2833_: *mut leanh::LeanObject,
    mut v_k_2834_: *mut leanh::LeanObject,
    mut v_toBind_2835_: *mut leanh::LeanObject,
    mut v___x_2836_: *mut leanh::LeanObject,
    mut v___x_2837_: *mut leanh::LeanObject,
    mut v_inst_2838_: *mut leanh::LeanObject,
    mut v_res_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_focusHyp_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v_p_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_focusHyp_2840_ = leanh::lean_ctor_get(v_res_2839_, 0);
                leanh::lean_inc_ref_n(v_focusHyp_2840_, 2);
                v_restHyps_2841_ = leanh::lean_ctor_get(v_res_2839_, 1);
                leanh::lean_inc_ref(v_restHyps_2841_);
                v_proof_2842_ = leanh::lean_ctor_get(v_res_2839_, 2);
                leanh::lean_inc_ref(v_proof_2842_);
                leanh::lean_dec_ref(v_res_2839_);
                v___x_2843_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_2840_);
                if leanh::lean_obj_tag(v___x_2843_) == 1 {
                    leanh::lean_dec(v_inst_2838_);
                    leanh::lean_dec_ref(v___x_2837_);
                    leanh::lean_dec_ref(v___x_2836_);
                    v_val_2844_ = leanh::lean_ctor_get(v___x_2843_, 0);
                    leanh::lean_inc(v_val_2844_);
                    leanh::lean_dec_ref_known(v___x_2843_, 1);
                    v_u_2845_ = leanh::lean_ctor_get(v_goal_2832_, 0);
                    v_00_u03c3s_2846_ = leanh::lean_ctor_get(v_goal_2832_, 1);
                    v_hyps_2847_ = leanh::lean_ctor_get(v_goal_2832_, 2);
                    v_target_2848_ = leanh::lean_ctor_get(v_goal_2832_, 3);
                    v_isSharedCheck_2867_ = (!leanh::lean_is_exclusive(v_goal_2832_)) as u8;
                    if v_isSharedCheck_2867_ == 0 {
                        v___x_2850_ = v_goal_2832_;
                        v_isShared_2851_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_target_2848_);
                        leanh::lean_inc(v_hyps_2847_);
                        leanh::lean_inc(v_00_u03c3s_2846_);
                        leanh::lean_inc(v_u_2845_);
                        leanh::lean_dec(v_goal_2832_);
                        v___x_2850_ = leanh::lean_box(0);
                        v_isShared_2851_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2843_);
                    leanh::lean_dec_ref(v_proof_2842_);
                    leanh::lean_dec_ref(v_restHyps_2841_);
                    leanh::lean_dec_ref(v_focusHyp_2840_);
                    leanh::lean_dec(v_toBind_2835_);
                    leanh::lean_dec(v_k_2834_);
                    leanh::lean_dec(v_toPure_2833_);
                    leanh::lean_dec_ref(v_goal_2832_);
                    v___x_2868_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
                    v___x_2869_ = l_Lean_throwError___redArg(v___x_2836_, v___x_2837_, v___x_2868_);
                    v___x_2870_ = leanh::lean_apply_2(
                        v_inst_2838_,
                        leanh::lean_box(0),
                        v___x_2869_,
                    );
                    return v___x_2870_;
                }
            }
            1 => {
                v_p_2852_ = leanh::lean_ctor_get(v_val_2844_, 2);
                leanh::lean_inc_ref(v_p_2852_);
                leanh::lean_dec(v_val_2844_);
                v___x_2853_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__0;
                v___x_2854_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__1;
                v___x_2855_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__2;
                v___x_2856_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4;
                v___x_2857_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2845_);
                v___x_2858_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2858_, 0, v_u_2845_);
                leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                leanh::lean_inc_ref(v_target_2848_);
                leanh::lean_inc_ref(v_restHyps_2841_);
                leanh::lean_inc_ref_n(v_00_u03c3s_2846_, 2);
                leanh::lean_inc_ref(v___x_2858_);
                v___f_2859_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__0
                        as *mut core::ffi::c_void,
                    12,
                    11,
                );
                leanh::lean_closure_set(v___f_2859_, 0, v___x_2853_);
                leanh::lean_closure_set(v___f_2859_, 1, v___x_2854_);
                leanh::lean_closure_set(v___f_2859_, 2, v___x_2855_);
                leanh::lean_closure_set(v___f_2859_, 3, v___x_2858_);
                leanh::lean_closure_set(v___f_2859_, 4, v_00_u03c3s_2846_);
                leanh::lean_closure_set(v___f_2859_, 5, v_hyps_2847_);
                leanh::lean_closure_set(v___f_2859_, 6, v_restHyps_2841_);
                leanh::lean_closure_set(v___f_2859_, 7, v_focusHyp_2840_);
                leanh::lean_closure_set(v___f_2859_, 8, v_target_2848_);
                leanh::lean_closure_set(v___f_2859_, 9, v_proof_2842_);
                leanh::lean_closure_set(v___f_2859_, 10, v_toPure_2833_);
                v___x_2860_ = l_Lean_mkConst(v___x_2856_, v___x_2858_);
                v___x_2861_ =
                    l_Lean_mkApp3(v___x_2860_, v_00_u03c3s_2846_, v_p_2852_, v_target_2848_);
                if v_isShared_2851_ == 0 {
                    leanh::lean_ctor_set(v___x_2850_, 3, v___x_2861_);
                    leanh::lean_ctor_set(v___x_2850_, 2, v_restHyps_2841_);
                    v___x_2863_ = v___x_2850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_u_2845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_00_u03c3s_2846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_restHyps_2841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 3, v___x_2861_);
                    v___x_2863_ = v_reuseFailAlloc_2866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2864_ = leanh::lean_apply_1(v_k_2834_, v___x_2863_);
                v___x_2865_ = leanh::lean_apply_4(
                    v_toBind_2835_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2864_,
                    v___f_2859_,
                );
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2871_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__0,
    );
    v___x_2873_ = l_StateRefT_x27_instMonad___redArg(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_2879_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2879_, 0, v___x_2878_);
    return v___f_2879_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_2881_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2881_, 0, v___x_2880_);
    return v___f_2881_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___f_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__7,
    );
    v___f_2883_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__6,
    );
    v___x_2884_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2884_, 0, v___f_2883_);
    leanh::lean_ctor_set(v___x_2884_, 1, v___f_2882_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8,
    );
    v___f_2886_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2886_, 0, v___x_2885_);
    return v___f_2886_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__8,
    );
    v___f_2888_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2888_, 0, v___x_2887_);
    return v___f_2888_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___f_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2889_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__10,
    );
    v___f_2890_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__9,
    );
    v___x_2891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2891_, 0, v___f_2890_);
    leanh::lean_ctor_set(v___x_2891_, 1, v___f_2889_);
    return v___x_2891_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_2897_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__15;
    v___x_2898_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__14;
    v___x_2899_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_2898_,
        v___x_2897_,
        v___x_2896_,
    );
    return v___x_2899_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2900_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__16,
    );
    v___f_2901_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__13;
    v___f_2902_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__12;
    v___x_2903_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_2902_,
        v___f_2901_,
        v___x_2900_,
    );
    return v___x_2903_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(
    mut v_inst_2904_: *mut leanh::LeanObject,
    mut v_inst_2905_: *mut leanh::LeanObject,
    mut v_goal_2906_: *mut leanh::LeanObject,
    mut v_ref_2907_: *mut leanh::LeanObject,
    mut v_k_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v_toFunctor_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___f_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v_unused_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut v_unused_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2909_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1,
                );
                v_toApplicative_2910_ = leanh::lean_ctor_get(v___x_2909_, 0);
                v_toFunctor_2911_ = leanh::lean_ctor_get(v_toApplicative_2910_, 0);
                v_toSeq_2912_ = leanh::lean_ctor_get(v_toApplicative_2910_, 2);
                v_toSeqLeft_2913_ = leanh::lean_ctor_get(v_toApplicative_2910_, 3);
                v_toSeqRight_2914_ = leanh::lean_ctor_get(v_toApplicative_2910_, 4);
                v___f_2915_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2;
                v___f_2916_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2911_, 2);
                v___f_2917_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2917_, 0, v_toFunctor_2911_);
                v___f_2918_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2918_, 0, v_toFunctor_2911_);
                v___x_2919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2919_, 0, v___f_2917_);
                leanh::lean_ctor_set(v___x_2919_, 1, v___f_2918_);
                leanh::lean_inc(v_toSeqRight_2914_);
                v___f_2920_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2920_, 0, v_toSeqRight_2914_);
                leanh::lean_inc(v_toSeqLeft_2913_);
                v___f_2921_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2921_, 0, v_toSeqLeft_2913_);
                leanh::lean_inc(v_toSeq_2912_);
                v___f_2922_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2922_, 0, v_toSeq_2912_);
                v___x_2923_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2923_, 0, v___x_2919_);
                leanh::lean_ctor_set(v___x_2923_, 1, v___f_2915_);
                leanh::lean_ctor_set(v___x_2923_, 2, v___f_2922_);
                leanh::lean_ctor_set(v___x_2923_, 3, v___f_2921_);
                leanh::lean_ctor_set(v___x_2923_, 4, v___f_2920_);
                v___x_2924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2924_, 0, v___x_2923_);
                leanh::lean_ctor_set(v___x_2924_, 1, v___f_2916_);
                v___x_2925_ = l_StateRefT_x27_instMonad___redArg(v___x_2924_);
                v_toApplicative_2926_ = leanh::lean_ctor_get(v___x_2925_, 0);
                v_isSharedCheck_2966_ = (!leanh::lean_is_exclusive(v___x_2925_)) as u8;
                if v_isSharedCheck_2966_ == 0 {
                    v_unused_2967_ = leanh::lean_ctor_get(v___x_2925_, 1);
                    leanh::lean_dec(v_unused_2967_);
                    v___x_2928_ = v___x_2925_;
                    v_isShared_2929_ = v_isSharedCheck_2966_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2926_);
                    leanh::lean_dec(v___x_2925_);
                    v___x_2928_ = leanh::lean_box(0);
                    v_isShared_2929_ = v_isSharedCheck_2966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2930_ = leanh::lean_ctor_get(v_toApplicative_2926_, 0);
                v_toSeq_2931_ = leanh::lean_ctor_get(v_toApplicative_2926_, 2);
                v_toSeqLeft_2932_ = leanh::lean_ctor_get(v_toApplicative_2926_, 3);
                v_toSeqRight_2933_ = leanh::lean_ctor_get(v_toApplicative_2926_, 4);
                v_isSharedCheck_2964_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2926_)) as u8;
                if v_isSharedCheck_2964_ == 0 {
                    v_unused_2965_ = leanh::lean_ctor_get(v_toApplicative_2926_, 1);
                    leanh::lean_dec(v_unused_2965_);
                    v___x_2935_ = v_toApplicative_2926_;
                    v_isShared_2936_ = v_isSharedCheck_2964_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2933_);
                    leanh::lean_inc(v_toSeqLeft_2932_);
                    leanh::lean_inc(v_toSeq_2931_);
                    leanh::lean_inc(v_toFunctor_2930_);
                    leanh::lean_dec(v_toApplicative_2926_);
                    v___x_2935_ = leanh::lean_box(0);
                    v_isShared_2936_ = v_isSharedCheck_2964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2937_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4;
                v___f_2938_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2930_);
                v___f_2939_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2939_, 0, v_toFunctor_2930_);
                v___f_2940_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2940_, 0, v_toFunctor_2930_);
                v___x_2941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2941_, 0, v___f_2939_);
                leanh::lean_ctor_set(v___x_2941_, 1, v___f_2940_);
                v___f_2942_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2942_, 0, v_toSeqRight_2933_);
                v___f_2943_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2943_, 0, v_toSeqLeft_2932_);
                v___f_2944_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2944_, 0, v_toSeq_2931_);
                if v_isShared_2936_ == 0 {
                    leanh::lean_ctor_set(v___x_2935_, 4, v___f_2942_);
                    leanh::lean_ctor_set(v___x_2935_, 3, v___f_2943_);
                    leanh::lean_ctor_set(v___x_2935_, 2, v___f_2944_);
                    leanh::lean_ctor_set(v___x_2935_, 1, v___f_2937_);
                    leanh::lean_ctor_set(v___x_2935_, 0, v___x_2941_);
                    v___x_2946_ = v___x_2935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___f_2937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 2, v___f_2944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 3, v___f_2943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 4, v___f_2942_);
                    v___x_2946_ = v_reuseFailAlloc_2963_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2929_ == 0 {
                    leanh::lean_ctor_set(v___x_2928_, 1, v___f_2938_);
                    leanh::lean_ctor_set(v___x_2928_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2928_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2962_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___f_2938_);
                    v___x_2948_ = v_reuseFailAlloc_2962_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2949_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11,
                );
                v___x_2950_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17,
                );
                v_toMonadRef_2951_ = leanh::lean_ctor_get(v___x_2950_, 0);
                v___x_2952_ = l_Lean_Meta_instAddMessageContextMetaM;
                leanh::lean_inc_ref(v___x_2948_);
                v___x_2953_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_2952_,
                    v___x_2948_,
                );
                leanh::lean_inc_ref(v_toMonadRef_2951_);
                v___x_2954_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2954_, 0, v___x_2949_);
                leanh::lean_ctor_set(v___x_2954_, 1, v_toMonadRef_2951_);
                leanh::lean_ctor_set(v___x_2954_, 2, v___x_2953_);
                v_toApplicative_2955_ = leanh::lean_ctor_get(v_inst_2904_, 0);
                leanh::lean_inc_ref(v_toApplicative_2955_);
                v_toBind_2956_ = leanh::lean_ctor_get(v_inst_2904_, 1);
                leanh::lean_inc_n(v_toBind_2956_, 2);
                leanh::lean_dec_ref(v_inst_2904_);
                v_toPure_2957_ = leanh::lean_ctor_get(v_toApplicative_2955_, 1);
                leanh::lean_inc(v_toPure_2957_);
                leanh::lean_dec_ref(v_toApplicative_2955_);
                leanh::lean_inc_ref(v_goal_2906_);
                v___x_2958_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___x_2958_, 0, v_goal_2906_);
                leanh::lean_closure_set(v___x_2958_, 1, v_ref_2907_);
                leanh::lean_inc(v_inst_2905_);
                v___x_2959_ = leanh::lean_apply_2(
                    v_inst_2905_,
                    leanh::lean_box(0),
                    v___x_2958_,
                );
                v___f_2960_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1
                        as *mut core::ffi::c_void,
                    8,
                    7,
                );
                leanh::lean_closure_set(v___f_2960_, 0, v_goal_2906_);
                leanh::lean_closure_set(v___f_2960_, 1, v_toPure_2957_);
                leanh::lean_closure_set(v___f_2960_, 2, v_k_2908_);
                leanh::lean_closure_set(v___f_2960_, 3, v_toBind_2956_);
                leanh::lean_closure_set(v___f_2960_, 4, v___x_2948_);
                leanh::lean_closure_set(v___f_2960_, 5, v___x_2954_);
                leanh::lean_closure_set(v___f_2960_, 6, v_inst_2905_);
                v___x_2961_ = leanh::lean_apply_4(
                    v_toBind_2956_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2959_,
                    v___f_2960_,
                );
                return v___x_2961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert(
    mut v_m_2968_: *mut leanh::LeanObject,
    mut v_inst_2969_: *mut leanh::LeanObject,
    mut v_inst_2970_: *mut leanh::LeanObject,
    mut v_goal_2971_: *mut leanh::LeanObject,
    mut v_ref_2972_: *mut leanh::LeanObject,
    mut v_k_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2974_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg(
        v_inst_2969_,
        v_inst_2970_,
        v_goal_2971_,
        v_ref_2972_,
        v_k_2973_,
    );
    return v___x_2974_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0(
    mut v_inst_2975_: *mut leanh::LeanObject,
    mut v_x_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2977_ = leanh::lean_ctor_get(v_x_2976_, 0);
    leanh::lean_inc(v_fst_2977_);
    v_snd_2978_ = leanh::lean_ctor_get(v_x_2976_, 1);
    leanh::lean_inc(v_snd_2978_);
    leanh::lean_dec_ref(v_x_2976_);
    v___x_2979_ =
        leanh::lean_alloc_closure(l_Lean_Meta_mkEq___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___x_2979_, 0, v_snd_2978_);
    leanh::lean_closure_set(v___x_2979_, 1, v_fst_2977_);
    v___x_2980_ = leanh::lean_apply_2(v_inst_2975_, leanh::lean_box(0), v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(
    mut v_hypName_2981_: *mut leanh::LeanObject,
    mut v___y_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
    mut v___y_2985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Lean_Core_mkFreshUserName(v_hypName_2981_, v___y_2984_, v___y_2985_);
    return v___x_2987_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed(
    mut v_hypName_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
    mut v___y_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2994_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1(
        v_hypName_2988_,
        v___y_2989_,
        v___y_2990_,
        v___y_2991_,
        v___y_2992_,
    );
    leanh::lean_dec(v___y_2992_);
    leanh::lean_dec_ref(v___y_2991_);
    leanh::lean_dec(v___y_2990_);
    leanh::lean_dec_ref(v___y_2989_);
    return v_res_2994_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__2(
    mut v_it_2995_: *mut leanh::LeanObject,
    mut v_acc_2996_: *mut leanh::LeanObject,
    mut v_recur_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v___x_3004_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2998_ = leanh::lean_ctor_get(v_it_2995_, 0);
                v_start_2999_ = leanh::lean_ctor_get(v_it_2995_, 1);
                v_stop_3000_ = leanh::lean_ctor_get(v_it_2995_, 2);
                v_isSharedCheck_3013_ = (!leanh::lean_is_exclusive(v_it_2995_)) as u8;
                if v_isSharedCheck_3013_ == 0 {
                    v___x_3002_ = v_it_2995_;
                    v_isShared_3003_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3000_);
                    leanh::lean_inc(v_start_2999_);
                    leanh::lean_inc(v_array_2998_);
                    leanh::lean_dec(v_it_2995_);
                    v___x_3002_ = leanh::lean_box(0);
                    v_isShared_3003_ = v_isSharedCheck_3013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3004_ = lean_nat_dec_lt(v_start_2999_, v_stop_3000_);
                if v___x_3004_ == 0 {
                    leanh::lean_del_object(v___x_3002_);
                    leanh::lean_dec(v_stop_3000_);
                    leanh::lean_dec(v_start_2999_);
                    leanh::lean_dec_ref(v_array_2998_);
                    leanh::lean_dec_ref(v_recur_2997_);
                    return v_acc_2996_;
                } else {
                    v___x_3005_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3006_ = lean_nat_add(v_start_2999_, v___x_3005_);
                    leanh::lean_inc_ref(v_array_2998_);
                    if v_isShared_3003_ == 0 {
                        leanh::lean_ctor_set(v___x_3002_, 1, v___x_3006_);
                        v___x_3008_ = v___x_3002_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3012_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_array_2998_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_3006_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_stop_3000_);
                        v___x_3008_ = v_reuseFailAlloc_3012_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3009_ = lean_array_fget(v_array_2998_, v_start_2999_);
                leanh::lean_dec(v_start_2999_);
                leanh::lean_dec_ref(v_array_2998_);
                v___x_3010_ = lean_array_push(v_acc_2996_, v___x_3009_);
                v___x_3011_ = leanh::lean_apply_3(
                    v_recur_2997_,
                    v___x_3008_,
                    v___x_3010_,
                    leanh::lean_box(0),
                );
                return v___x_3011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3(
    mut v_u_3014_: *mut leanh::LeanObject,
    mut v_x1_3015_: *mut leanh::LeanObject,
    mut v_x2_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ =
        l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(v_u_3014_, v_x1_3015_, v_x2_3016_);
    return v___x_3017_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(
    mut v_toApplicative_3018_: *mut leanh::LeanObject,
    mut v_i_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
    mut v_____do__lift_3021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3022_ = leanh::lean_ctor_get(v_toApplicative_3018_, 1);
    leanh::lean_inc(v_toPure_3022_);
    leanh::lean_dec_ref(v_toApplicative_3018_);
    v___x_3023_ = leanh::lean_unsigned_to_nat(1);
    v___x_3024_ = lean_nat_add(v_i_3019_, v___x_3023_);
    v___x_3025_ = lean_name_append_index_after(v_____do__lift_3021_, v___x_3024_);
    v___x_3026_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3026_, 0, v___x_3025_);
    leanh::lean_ctor_set(v___x_3026_, 1, v_a_3020_);
    v___x_3027_ =
        leanh::lean_apply_2(v_toPure_3022_, leanh::lean_box(0), v___x_3026_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed(
    mut v_toApplicative_3028_: *mut leanh::LeanObject,
    mut v_i_3029_: *mut leanh::LeanObject,
    mut v_a_3030_: *mut leanh::LeanObject,
    mut v_____do__lift_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4(
        v_toApplicative_3028_,
        v_i_3029_,
        v_a_3030_,
        v_____do__lift_3031_,
    );
    leanh::lean_dec(v_i_3029_);
    return v_res_3032_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(
    mut v___x_3033_: *mut leanh::LeanObject,
    mut v___y_3034_: *mut leanh::LeanObject,
    mut v___y_3035_: *mut leanh::LeanObject,
    mut v___y_3036_: *mut leanh::LeanObject,
    mut v___y_3037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_Core_mkFreshUserName(v___x_3033_, v___y_3036_, v___y_3037_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5___boxed(
    mut v___x_3040_: *mut leanh::LeanObject,
    mut v___y_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
    mut v___y_3043_: *mut leanh::LeanObject,
    mut v___y_3044_: *mut leanh::LeanObject,
    mut v___y_3045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3046_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__5(
        v___x_3040_,
        v___y_3041_,
        v___y_3042_,
        v___y_3043_,
        v___y_3044_,
    );
    leanh::lean_dec(v___y_3044_);
    leanh::lean_dec_ref(v___y_3043_);
    leanh::lean_dec(v___y_3042_);
    leanh::lean_dec_ref(v___y_3041_);
    return v_res_3046_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6(
    mut v_toApplicative_3052_: *mut leanh::LeanObject,
    mut v_inst_3053_: *mut leanh::LeanObject,
    mut v_toBind_3054_: *mut leanh::LeanObject,
    mut v_i_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_x_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3058_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3058_, 0, v_toApplicative_3052_);
    leanh::lean_closure_set(v___f_3058_, 1, v_i_3055_);
    leanh::lean_closure_set(v___f_3058_, 2, v_a_3056_);
    v___f_3059_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__2;
    v___x_3060_ = leanh::lean_apply_2(v_inst_3053_, leanh::lean_box(0), v___f_3059_);
    v___x_3061_ = leanh::lean_apply_4(
        v_toBind_3054_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3060_,
        v___f_3058_,
    );
    return v___x_3061_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7(
    mut v_toApplicative_3062_: *mut leanh::LeanObject,
    mut v_00_u03c6_3063_: *mut leanh::LeanObject,
    mut v_____do__lift_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3065_ = leanh::lean_ctor_get(v_toApplicative_3062_, 1);
    leanh::lean_inc(v_toPure_3065_);
    leanh::lean_dec_ref(v_toApplicative_3062_);
    v___x_3066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3066_, 0, v_____do__lift_3064_);
    leanh::lean_ctor_set(v___x_3066_, 1, v_00_u03c6_3063_);
    v___x_3067_ =
        leanh::lean_apply_2(v_toPure_3065_, leanh::lean_box(0), v___x_3066_);
    return v___x_3067_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(
    mut v_hypName_3068_: *mut leanh::LeanObject,
    mut v_uniq_3069_: *mut leanh::LeanObject,
    mut v_toApplicative_3070_: *mut leanh::LeanObject,
    mut v_ss_3071_: *mut leanh::LeanObject,
    mut v_hyps_3072_: *mut leanh::LeanObject,
    mut v___x_3073_: u8,
    mut v___x_3074_: u8,
    mut v___x_3075_: u8,
    mut v_inst_3076_: *mut leanh::LeanObject,
    mut v_toBind_3077_: *mut leanh::LeanObject,
    mut v_____do__lift_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3079_, 0, v_hypName_3068_);
    leanh::lean_ctor_set(v___x_3079_, 1, v_uniq_3069_);
    leanh::lean_ctor_set(v___x_3079_, 2, v_____do__lift_3078_);
    v_00_u03c6_3080_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_3079_);
    v___f_3081_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__7 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3081_, 0, v_toApplicative_3070_);
    leanh::lean_closure_set(v___f_3081_, 1, v_00_u03c6_3080_);
    v___x_3082_ = leanh::lean_box((v___x_3073_) as usize);
    v___x_3083_ = leanh::lean_box((v___x_3074_) as usize);
    v___x_3084_ = leanh::lean_box((v___x_3073_) as usize);
    v___x_3085_ = leanh::lean_box((v___x_3074_) as usize);
    v___x_3086_ = leanh::lean_box((v___x_3075_) as usize);
    v___x_3087_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3087_, 0, v_ss_3071_);
    leanh::lean_closure_set(v___x_3087_, 1, v_hyps_3072_);
    leanh::lean_closure_set(v___x_3087_, 2, v___x_3082_);
    leanh::lean_closure_set(v___x_3087_, 3, v___x_3083_);
    leanh::lean_closure_set(v___x_3087_, 4, v___x_3084_);
    leanh::lean_closure_set(v___x_3087_, 5, v___x_3085_);
    leanh::lean_closure_set(v___x_3087_, 6, v___x_3086_);
    v___x_3088_ = leanh::lean_apply_2(v_inst_3076_, leanh::lean_box(0), v___x_3087_);
    v___x_3089_ = leanh::lean_apply_4(
        v_toBind_3077_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3088_,
        v___f_3081_,
    );
    return v___x_3089_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed(
    mut v_hypName_3090_: *mut leanh::LeanObject,
    mut v_uniq_3091_: *mut leanh::LeanObject,
    mut v_toApplicative_3092_: *mut leanh::LeanObject,
    mut v_ss_3093_: *mut leanh::LeanObject,
    mut v_hyps_3094_: *mut leanh::LeanObject,
    mut v___x_3095_: *mut leanh::LeanObject,
    mut v___x_3096_: *mut leanh::LeanObject,
    mut v___x_3097_: *mut leanh::LeanObject,
    mut v_inst_3098_: *mut leanh::LeanObject,
    mut v_toBind_3099_: *mut leanh::LeanObject,
    mut v_____do__lift_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1119__boxed_3101_: u8 = 0;
    let mut v___x_1120__boxed_3102_: u8 = 0;
    let mut v___x_1121__boxed_3103_: u8 = 0;
    let mut v_res_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1119__boxed_3101_ = (leanh::lean_unbox(v___x_3095_) as u8);
    v___x_1120__boxed_3102_ = (leanh::lean_unbox(v___x_3096_) as u8);
    v___x_1121__boxed_3103_ = (leanh::lean_unbox(v___x_3097_) as u8);
    v_res_3104_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8(
        v_hypName_3090_,
        v_uniq_3091_,
        v_toApplicative_3092_,
        v_ss_3093_,
        v_hyps_3094_,
        v___x_1119__boxed_3101_,
        v___x_1120__boxed_3102_,
        v___x_1121__boxed_3103_,
        v_inst_3098_,
        v_toBind_3099_,
        v_____do__lift_3100_,
    );
    return v_res_3104_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(
    mut v_hypName_3105_: *mut leanh::LeanObject,
    mut v_toApplicative_3106_: *mut leanh::LeanObject,
    mut v_ss_3107_: *mut leanh::LeanObject,
    mut v_hyps_3108_: *mut leanh::LeanObject,
    mut v___x_3109_: u8,
    mut v_inst_3110_: *mut leanh::LeanObject,
    mut v_toBind_3111_: *mut leanh::LeanObject,
    mut v_00_u03c6_3112_: *mut leanh::LeanObject,
    mut v_uniq_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3114_: u8 = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = 1;
    v___x_3115_ = 1;
    v___x_3116_ = leanh::lean_box((v___x_3109_) as usize);
    v___x_3117_ = leanh::lean_box((v___x_3114_) as usize);
    v___x_3118_ = leanh::lean_box((v___x_3115_) as usize);
    leanh::lean_inc(v_toBind_3111_);
    leanh::lean_inc(v_inst_3110_);
    leanh::lean_inc_ref(v_ss_3107_);
    v___f_3119_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_3119_, 0, v_hypName_3105_);
    leanh::lean_closure_set(v___f_3119_, 1, v_uniq_3113_);
    leanh::lean_closure_set(v___f_3119_, 2, v_toApplicative_3106_);
    leanh::lean_closure_set(v___f_3119_, 3, v_ss_3107_);
    leanh::lean_closure_set(v___f_3119_, 4, v_hyps_3108_);
    leanh::lean_closure_set(v___f_3119_, 5, v___x_3116_);
    leanh::lean_closure_set(v___f_3119_, 6, v___x_3117_);
    leanh::lean_closure_set(v___f_3119_, 7, v___x_3118_);
    leanh::lean_closure_set(v___f_3119_, 8, v_inst_3110_);
    leanh::lean_closure_set(v___f_3119_, 9, v_toBind_3111_);
    v___x_3120_ = leanh::lean_box((v___x_3109_) as usize);
    v___x_3121_ = leanh::lean_box((v___x_3114_) as usize);
    v___x_3122_ = leanh::lean_box((v___x_3109_) as usize);
    v___x_3123_ = leanh::lean_box((v___x_3114_) as usize);
    v___x_3124_ = leanh::lean_box((v___x_3115_) as usize);
    v___x_3125_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3125_, 0, v_ss_3107_);
    leanh::lean_closure_set(v___x_3125_, 1, v_00_u03c6_3112_);
    leanh::lean_closure_set(v___x_3125_, 2, v___x_3120_);
    leanh::lean_closure_set(v___x_3125_, 3, v___x_3121_);
    leanh::lean_closure_set(v___x_3125_, 4, v___x_3122_);
    leanh::lean_closure_set(v___x_3125_, 5, v___x_3123_);
    leanh::lean_closure_set(v___x_3125_, 6, v___x_3124_);
    v___x_3126_ = leanh::lean_apply_2(v_inst_3110_, leanh::lean_box(0), v___x_3125_);
    v___x_3127_ = leanh::lean_apply_4(
        v_toBind_3111_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3126_,
        v___f_3119_,
    );
    return v___x_3127_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed(
    mut v_hypName_3128_: *mut leanh::LeanObject,
    mut v_toApplicative_3129_: *mut leanh::LeanObject,
    mut v_ss_3130_: *mut leanh::LeanObject,
    mut v_hyps_3131_: *mut leanh::LeanObject,
    mut v___x_3132_: *mut leanh::LeanObject,
    mut v_inst_3133_: *mut leanh::LeanObject,
    mut v_toBind_3134_: *mut leanh::LeanObject,
    mut v_00_u03c6_3135_: *mut leanh::LeanObject,
    mut v_uniq_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1154__boxed_3137_: u8 = 0;
    let mut v_res_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1154__boxed_3137_ = (leanh::lean_unbox(v___x_3132_) as u8);
    v_res_3138_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9(
        v_hypName_3128_,
        v_toApplicative_3129_,
        v_ss_3130_,
        v_hyps_3131_,
        v___x_1154__boxed_3137_,
        v_inst_3133_,
        v_toBind_3134_,
        v_00_u03c6_3135_,
        v_uniq_3136_,
    );
    return v_res_3138_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(
    mut v_u_3139_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3140_: *mut leanh::LeanObject,
    mut v_hypName_3141_: *mut leanh::LeanObject,
    mut v_toApplicative_3142_: *mut leanh::LeanObject,
    mut v_ss_3143_: *mut leanh::LeanObject,
    mut v_hyps_3144_: *mut leanh::LeanObject,
    mut v___x_3145_: u8,
    mut v_inst_3146_: *mut leanh::LeanObject,
    mut v_toBind_3147_: *mut leanh::LeanObject,
    mut v___f_3148_: *mut leanh::LeanObject,
    mut v_eqs_3149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eqs_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eqs_3150_ = lean_array_to_list(v_eqs_3149_);
    v_00_u03c6_3151_ = l_Lean_mkAndN(v_eqs_3150_);
    v_00_u03c6_3152_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(
        v_u_3139_,
        v_00_u03c3s_3140_,
        v_00_u03c6_3151_,
    );
    v___x_3153_ = leanh::lean_box((v___x_3145_) as usize);
    leanh::lean_inc(v_toBind_3147_);
    leanh::lean_inc(v_inst_3146_);
    v___f_3154_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_3154_, 0, v_hypName_3141_);
    leanh::lean_closure_set(v___f_3154_, 1, v_toApplicative_3142_);
    leanh::lean_closure_set(v___f_3154_, 2, v_ss_3143_);
    leanh::lean_closure_set(v___f_3154_, 3, v_hyps_3144_);
    leanh::lean_closure_set(v___f_3154_, 4, v___x_3153_);
    leanh::lean_closure_set(v___f_3154_, 5, v_inst_3146_);
    leanh::lean_closure_set(v___f_3154_, 6, v_toBind_3147_);
    leanh::lean_closure_set(v___f_3154_, 7, v_00_u03c6_3152_);
    v___x_3155_ = leanh::lean_apply_2(v_inst_3146_, leanh::lean_box(0), v___f_3148_);
    v___x_3156_ = leanh::lean_apply_4(
        v_toBind_3147_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3155_,
        v___f_3154_,
    );
    return v___x_3156_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed(
    mut v_u_3157_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3158_: *mut leanh::LeanObject,
    mut v_hypName_3159_: *mut leanh::LeanObject,
    mut v_toApplicative_3160_: *mut leanh::LeanObject,
    mut v_ss_3161_: *mut leanh::LeanObject,
    mut v_hyps_3162_: *mut leanh::LeanObject,
    mut v___x_3163_: *mut leanh::LeanObject,
    mut v_inst_3164_: *mut leanh::LeanObject,
    mut v_toBind_3165_: *mut leanh::LeanObject,
    mut v___f_3166_: *mut leanh::LeanObject,
    mut v_eqs_3167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1188__boxed_3168_: u8 = 0;
    let mut v_res_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1188__boxed_3168_ = (leanh::lean_unbox(v___x_3163_) as u8);
    v_res_3169_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10(
        v_u_3157_,
        v_00_u03c3s_3158_,
        v_hypName_3159_,
        v_toApplicative_3160_,
        v_ss_3161_,
        v_hyps_3162_,
        v___x_1188__boxed_3168_,
        v_inst_3164_,
        v_toBind_3165_,
        v___f_3166_,
        v_eqs_3167_,
    );
    return v_res_3169_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(
    mut v_u_3170_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3171_: *mut leanh::LeanObject,
    mut v_hypName_3172_: *mut leanh::LeanObject,
    mut v_toApplicative_3173_: *mut leanh::LeanObject,
    mut v_hyps_3174_: *mut leanh::LeanObject,
    mut v___x_3175_: u8,
    mut v_inst_3176_: *mut leanh::LeanObject,
    mut v_toBind_3177_: *mut leanh::LeanObject,
    mut v___f_3178_: *mut leanh::LeanObject,
    mut v_revertArgs_3179_: *mut leanh::LeanObject,
    mut v_inst_3180_: *mut leanh::LeanObject,
    mut v___f_3181_: *mut leanh::LeanObject,
    mut v_ss_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3186_: usize = 0;
    let mut v___x_3187_: usize = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = leanh::lean_box((v___x_3175_) as usize);
    leanh::lean_inc(v_toBind_3177_);
    leanh::lean_inc_ref(v_ss_3182_);
    v___f_3184_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__10___boxed
            as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_3184_, 0, v_u_3170_);
    leanh::lean_closure_set(v___f_3184_, 1, v_00_u03c3s_3171_);
    leanh::lean_closure_set(v___f_3184_, 2, v_hypName_3172_);
    leanh::lean_closure_set(v___f_3184_, 3, v_toApplicative_3173_);
    leanh::lean_closure_set(v___f_3184_, 4, v_ss_3182_);
    leanh::lean_closure_set(v___f_3184_, 5, v_hyps_3174_);
    leanh::lean_closure_set(v___f_3184_, 6, v___x_3183_);
    leanh::lean_closure_set(v___f_3184_, 7, v_inst_3176_);
    leanh::lean_closure_set(v___f_3184_, 8, v_toBind_3177_);
    leanh::lean_closure_set(v___f_3184_, 9, v___f_3178_);
    v___x_3185_ = l_Array_zip___redArg(v_revertArgs_3179_, v_ss_3182_);
    leanh::lean_dec_ref(v_ss_3182_);
    v_sz_3186_ = lean_array_size(v___x_3185_);
    v___x_3187_ = 0usize;
    v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_3180_,
        v___f_3181_,
        v_sz_3186_,
        v___x_3187_,
        v___x_3185_,
    );
    v___x_3189_ = leanh::lean_apply_4(
        v_toBind_3177_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3188_,
        v___f_3184_,
    );
    return v___x_3189_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed(
    mut v_u_3190_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3191_: *mut leanh::LeanObject,
    mut v_hypName_3192_: *mut leanh::LeanObject,
    mut v_toApplicative_3193_: *mut leanh::LeanObject,
    mut v_hyps_3194_: *mut leanh::LeanObject,
    mut v___x_3195_: *mut leanh::LeanObject,
    mut v_inst_3196_: *mut leanh::LeanObject,
    mut v_toBind_3197_: *mut leanh::LeanObject,
    mut v___f_3198_: *mut leanh::LeanObject,
    mut v_revertArgs_3199_: *mut leanh::LeanObject,
    mut v_inst_3200_: *mut leanh::LeanObject,
    mut v___f_3201_: *mut leanh::LeanObject,
    mut v_ss_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1205__boxed_3203_: u8 = 0;
    let mut v_res_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1205__boxed_3203_ = (leanh::lean_unbox(v___x_3195_) as u8);
    v_res_3204_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11(
        v_u_3190_,
        v_00_u03c3s_3191_,
        v_hypName_3192_,
        v_toApplicative_3193_,
        v_hyps_3194_,
        v___x_1205__boxed_3203_,
        v_inst_3196_,
        v_toBind_3197_,
        v___f_3198_,
        v_revertArgs_3199_,
        v_inst_3200_,
        v___f_3201_,
        v_ss_3202_,
    );
    leanh::lean_dec_ref(v_revertArgs_3199_);
    return v_res_3204_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(
    mut v_toApplicative_3213_: *mut leanh::LeanObject,
    mut v_u_3214_: *mut leanh::LeanObject,
    mut v_fst_3215_: *mut leanh::LeanObject,
    mut v_revertArgs_3216_: *mut leanh::LeanObject,
    mut v_snd_3217_: *mut leanh::LeanObject,
    mut v_prf_3218_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3219_: *mut leanh::LeanObject,
    mut v_hyps_3220_: *mut leanh::LeanObject,
    mut v_target_3221_: *mut leanh::LeanObject,
    mut v_h_3222_: *mut leanh::LeanObject,
    mut v_____do__lift_3223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_3224_ = leanh::lean_ctor_get(v_toApplicative_3213_, 1);
    leanh::lean_inc(v_toPure_3224_);
    leanh::lean_dec_ref(v_toApplicative_3213_);
    v___x_3225_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1;
    v___x_3226_ = leanh::lean_box(0);
    v___x_3227_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3227_, 0, v_u_3214_);
    leanh::lean_ctor_set(v___x_3227_, 1, v___x_3226_);
    v___x_3228_ = l_Lean_mkConst(v___x_3225_, v___x_3227_);
    v___x_3229_ = l_Lean_mkAppN(v_fst_3215_, v_revertArgs_3216_);
    v___x_3230_ = l_Lean_mkAppN(v_snd_3217_, v_revertArgs_3216_);
    v___x_3231_ = l_Lean_mkAppN(v_prf_3218_, v_revertArgs_3216_);
    v_prf_3232_ = l_Lean_mkApp8(
        v___x_3228_,
        v_00_u03c3s_3219_,
        v_____do__lift_3223_,
        v_hyps_3220_,
        v___x_3229_,
        v_target_3221_,
        v_h_3222_,
        v___x_3230_,
        v___x_3231_,
    );
    v___x_3233_ =
        leanh::lean_apply_2(v_toPure_3224_, leanh::lean_box(0), v_prf_3232_);
    return v___x_3233_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed(
    mut v_toApplicative_3234_: *mut leanh::LeanObject,
    mut v_u_3235_: *mut leanh::LeanObject,
    mut v_fst_3236_: *mut leanh::LeanObject,
    mut v_revertArgs_3237_: *mut leanh::LeanObject,
    mut v_snd_3238_: *mut leanh::LeanObject,
    mut v_prf_3239_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3240_: *mut leanh::LeanObject,
    mut v_hyps_3241_: *mut leanh::LeanObject,
    mut v_target_3242_: *mut leanh::LeanObject,
    mut v_h_3243_: *mut leanh::LeanObject,
    mut v_____do__lift_3244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12(
        v_toApplicative_3234_,
        v_u_3235_,
        v_fst_3236_,
        v_revertArgs_3237_,
        v_snd_3238_,
        v_prf_3239_,
        v_00_u03c3s_3240_,
        v_hyps_3241_,
        v_target_3242_,
        v_h_3243_,
        v_____do__lift_3244_,
    );
    leanh::lean_dec_ref(v_revertArgs_3237_);
    return v_res_3245_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13(
    mut v_toApplicative_3246_: *mut leanh::LeanObject,
    mut v_u_3247_: *mut leanh::LeanObject,
    mut v_fst_3248_: *mut leanh::LeanObject,
    mut v_revertArgs_3249_: *mut leanh::LeanObject,
    mut v_snd_3250_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3251_: *mut leanh::LeanObject,
    mut v_hyps_3252_: *mut leanh::LeanObject,
    mut v_target_3253_: *mut leanh::LeanObject,
    mut v_h_3254_: *mut leanh::LeanObject,
    mut v_inst_3255_: *mut leanh::LeanObject,
    mut v_toBind_3256_: *mut leanh::LeanObject,
    mut v_prf_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_h_3254_);
    v___f_3258_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___boxed
            as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_3258_, 0, v_toApplicative_3246_);
    leanh::lean_closure_set(v___f_3258_, 1, v_u_3247_);
    leanh::lean_closure_set(v___f_3258_, 2, v_fst_3248_);
    leanh::lean_closure_set(v___f_3258_, 3, v_revertArgs_3249_);
    leanh::lean_closure_set(v___f_3258_, 4, v_snd_3250_);
    leanh::lean_closure_set(v___f_3258_, 5, v_prf_3257_);
    leanh::lean_closure_set(v___f_3258_, 6, v_00_u03c3s_3251_);
    leanh::lean_closure_set(v___f_3258_, 7, v_hyps_3252_);
    leanh::lean_closure_set(v___f_3258_, 8, v_target_3253_);
    leanh::lean_closure_set(v___f_3258_, 9, v_h_3254_);
    v___x_3259_ = leanh::lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_3259_, 0, v_h_3254_);
    v___x_3260_ = leanh::lean_apply_2(v_inst_3255_, leanh::lean_box(0), v___x_3259_);
    v___x_3261_ = leanh::lean_apply_4(
        v_toBind_3256_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3260_,
        v___f_3258_,
    );
    return v___x_3261_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14(
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v_u_3263_: *mut leanh::LeanObject,
    mut v_snd_3264_: *mut leanh::LeanObject,
    mut v_toApplicative_3265_: *mut leanh::LeanObject,
    mut v_revertArgs_3266_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3267_: *mut leanh::LeanObject,
    mut v_hyps_3268_: *mut leanh::LeanObject,
    mut v_target_3269_: *mut leanh::LeanObject,
    mut v_h_3270_: *mut leanh::LeanObject,
    mut v_inst_3271_: *mut leanh::LeanObject,
    mut v_toBind_3272_: *mut leanh::LeanObject,
    mut v_a_3273_: *mut leanh::LeanObject,
    mut v_n_3274_: *mut leanh::LeanObject,
    mut v_f_3275_: *mut leanh::LeanObject,
    mut v_k_3276_: *mut leanh::LeanObject,
    mut v_H_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_H_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_x27_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v___y_3262_, 2);
    v_H_3278_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v___y_3262_, v_H_3277_);
    leanh::lean_inc_n(v_u_3263_, 2);
    v___x_3279_ =
        l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_3263_, v___y_3262_, v_H_3278_, v_snd_3264_);
    v_fst_3280_ = leanh::lean_ctor_get(v___x_3279_, 0);
    leanh::lean_inc_n(v_fst_3280_, 2);
    v_snd_3281_ = leanh::lean_ctor_get(v___x_3279_, 1);
    leanh::lean_inc(v_snd_3281_);
    leanh::lean_dec_ref(v___x_3279_);
    leanh::lean_inc(v_toBind_3272_);
    v___f_3282_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__13 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_3282_, 0, v_toApplicative_3265_);
    leanh::lean_closure_set(v___f_3282_, 1, v_u_3263_);
    leanh::lean_closure_set(v___f_3282_, 2, v_fst_3280_);
    leanh::lean_closure_set(v___f_3282_, 3, v_revertArgs_3266_);
    leanh::lean_closure_set(v___f_3282_, 4, v_snd_3281_);
    leanh::lean_closure_set(v___f_3282_, 5, v_00_u03c3s_3267_);
    leanh::lean_closure_set(v___f_3282_, 6, v_hyps_3268_);
    leanh::lean_closure_set(v___f_3282_, 7, v_target_3269_);
    leanh::lean_closure_set(v___f_3282_, 8, v_h_3270_);
    leanh::lean_closure_set(v___f_3282_, 9, v_inst_3271_);
    leanh::lean_closure_set(v___f_3282_, 10, v_toBind_3272_);
    v___x_3283_ = lean_array_get_size(v_a_3273_);
    v___x_3284_ = l_Array_toSubarray___redArg(v_a_3273_, v_n_3274_, v___x_3283_);
    v___x_3285_ = l_Subarray_copy___redArg(v___x_3284_);
    v___x_3286_ = l_Lean_mkAppRev(v_f_3275_, v___x_3285_);
    leanh::lean_dec_ref(v___x_3285_);
    v_goal_x27_3287_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v_goal_x27_3287_, 0, v_u_3263_);
    leanh::lean_ctor_set(v_goal_x27_3287_, 1, v___y_3262_);
    leanh::lean_ctor_set(v_goal_x27_3287_, 2, v_fst_3280_);
    leanh::lean_ctor_set(v_goal_x27_3287_, 3, v___x_3286_);
    v___x_3288_ = leanh::lean_apply_1(v_k_3276_, v_goal_x27_3287_);
    v___x_3289_ = leanh::lean_apply_4(
        v_toBind_3272_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3288_,
        v___f_3282_,
    );
    return v___x_3289_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(
    mut v_u_3309_: *mut leanh::LeanObject,
    mut v_snd_3310_: *mut leanh::LeanObject,
    mut v_toApplicative_3311_: *mut leanh::LeanObject,
    mut v_revertArgs_3312_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3313_: *mut leanh::LeanObject,
    mut v_hyps_3314_: *mut leanh::LeanObject,
    mut v_target_3315_: *mut leanh::LeanObject,
    mut v_inst_3316_: *mut leanh::LeanObject,
    mut v_toBind_3317_: *mut leanh::LeanObject,
    mut v_a_3318_: *mut leanh::LeanObject,
    mut v_n_3319_: *mut leanh::LeanObject,
    mut v_f_3320_: *mut leanh::LeanObject,
    mut v_k_3321_: *mut leanh::LeanObject,
    mut v_fst_3322_: *mut leanh::LeanObject,
    mut v_revertArgsTypes_3323_: *mut leanh::LeanObject,
    mut v___x_3324_: *mut leanh::LeanObject,
    mut v___f_3325_: *mut leanh::LeanObject,
    mut v_h_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: usize = 0;
    let mut v___x_3337_: usize = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3333_ = lean_array_get_size(v_revertArgsTypes_3323_);
                v___x_3334_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___closed__9;
                v___x_3335_ = lean_nat_dec_lt(v___x_3324_, v___x_3333_);
                if v___x_3335_ == 0 {
                    leanh::lean_dec_ref(v___f_3325_);
                    leanh::lean_dec_ref(v_revertArgsTypes_3323_);
                    leanh::lean_inc_ref(v_00_u03c3s_3313_);
                    v___y_3328_ = v_00_u03c3s_3313_;
                    state = 1;
                    continue;
                } else {
                    v___x_3336_ = lean_usize_of_nat(v___x_3333_);
                    v___x_3337_ = 0usize;
                    leanh::lean_inc_ref(v_00_u03c3s_3313_);
                    v___x_3338_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3334_,
                        v___f_3325_,
                        v_revertArgsTypes_3323_,
                        v___x_3336_,
                        v___x_3337_,
                        v_00_u03c3s_3313_,
                    );
                    v___y_3328_ = v___x_3338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toBind_3317_);
                leanh::lean_inc(v_inst_3316_);
                v___f_3329_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__14
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                leanh::lean_closure_set(v___f_3329_, 0, v___y_3328_);
                leanh::lean_closure_set(v___f_3329_, 1, v_u_3309_);
                leanh::lean_closure_set(v___f_3329_, 2, v_snd_3310_);
                leanh::lean_closure_set(v___f_3329_, 3, v_toApplicative_3311_);
                leanh::lean_closure_set(v___f_3329_, 4, v_revertArgs_3312_);
                leanh::lean_closure_set(v___f_3329_, 5, v_00_u03c3s_3313_);
                leanh::lean_closure_set(v___f_3329_, 6, v_hyps_3314_);
                leanh::lean_closure_set(v___f_3329_, 7, v_target_3315_);
                leanh::lean_closure_set(v___f_3329_, 8, v_h_3326_);
                leanh::lean_closure_set(v___f_3329_, 9, v_inst_3316_);
                leanh::lean_closure_set(v___f_3329_, 10, v_toBind_3317_);
                leanh::lean_closure_set(v___f_3329_, 11, v_a_3318_);
                leanh::lean_closure_set(v___f_3329_, 12, v_n_3319_);
                leanh::lean_closure_set(v___f_3329_, 13, v_f_3320_);
                leanh::lean_closure_set(v___f_3329_, 14, v_k_3321_);
                v___x_3330_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_instantiateMVarsIfMVarApp___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___x_3330_, 0, v_fst_3322_);
                v___x_3331_ = leanh::lean_apply_2(
                    v_inst_3316_,
                    leanh::lean_box(0),
                    v___x_3330_,
                );
                v___x_3332_ = leanh::lean_apply_4(
                    v_toBind_3317_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3331_,
                    v___f_3329_,
                );
                return v___x_3332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3339_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_snd_3340_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_toApplicative_3341_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_revertArgs_3342_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_00_u03c3s_3343_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_hyps_3344_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_target_3345_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_inst_3346_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_toBind_3347_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_3348_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_n_3349_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_f_3350_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_k_3351_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_fst_3352_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_revertArgsTypes_3353_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_3354_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_3355_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_h_3356_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15(
        v_u_3339_,
        v_snd_3340_,
        v_toApplicative_3341_,
        v_revertArgs_3342_,
        v_00_u03c3s_3343_,
        v_hyps_3344_,
        v_target_3345_,
        v_inst_3346_,
        v_toBind_3347_,
        v_a_3348_,
        v_n_3349_,
        v_f_3350_,
        v_k_3351_,
        v_fst_3352_,
        v_revertArgsTypes_3353_,
        v___x_3354_,
        v___f_3355_,
        v_h_3356_,
    );
    leanh::lean_dec(v___x_3354_);
    return v_res_3357_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16(
    mut v_inst_3358_: *mut leanh::LeanObject,
    mut v_toBind_3359_: *mut leanh::LeanObject,
    mut v___f_3360_: *mut leanh::LeanObject,
    mut v_prfs_3361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = lean_array_to_list(v_prfs_3361_);
    v___x_3363_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkAndIntroN___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_3363_, 0, v___x_3362_);
    v___x_3364_ = leanh::lean_apply_2(v_inst_3358_, leanh::lean_box(0), v___x_3363_);
    v___x_3365_ = leanh::lean_apply_4(
        v_toBind_3359_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3364_,
        v___f_3360_,
    );
    return v___x_3365_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(
    mut v_u_3367_: *mut leanh::LeanObject,
    mut v_toApplicative_3368_: *mut leanh::LeanObject,
    mut v_revertArgs_3369_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3370_: *mut leanh::LeanObject,
    mut v_hyps_3371_: *mut leanh::LeanObject,
    mut v_target_3372_: *mut leanh::LeanObject,
    mut v_inst_3373_: *mut leanh::LeanObject,
    mut v_toBind_3374_: *mut leanh::LeanObject,
    mut v_a_3375_: *mut leanh::LeanObject,
    mut v_n_3376_: *mut leanh::LeanObject,
    mut v_f_3377_: *mut leanh::LeanObject,
    mut v_k_3378_: *mut leanh::LeanObject,
    mut v_revertArgsTypes_3379_: *mut leanh::LeanObject,
    mut v___x_3380_: *mut leanh::LeanObject,
    mut v___f_3381_: *mut leanh::LeanObject,
    mut v___x_3382_: *mut leanh::LeanObject,
    mut v_____x_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3389_: usize = 0;
    let mut v___x_3390_: usize = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3384_ = leanh::lean_ctor_get(v_____x_3383_, 0);
    leanh::lean_inc(v_fst_3384_);
    v_snd_3385_ = leanh::lean_ctor_get(v_____x_3383_, 1);
    leanh::lean_inc(v_snd_3385_);
    leanh::lean_dec_ref(v_____x_3383_);
    leanh::lean_inc_n(v_toBind_3374_, 2);
    leanh::lean_inc_n(v_inst_3373_, 2);
    leanh::lean_inc_ref(v_revertArgs_3369_);
    v___f_3386_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__15___boxed
            as *mut core::ffi::c_void,
        18,
        17,
    );
    leanh::lean_closure_set(v___f_3386_, 0, v_u_3367_);
    leanh::lean_closure_set(v___f_3386_, 1, v_snd_3385_);
    leanh::lean_closure_set(v___f_3386_, 2, v_toApplicative_3368_);
    leanh::lean_closure_set(v___f_3386_, 3, v_revertArgs_3369_);
    leanh::lean_closure_set(v___f_3386_, 4, v_00_u03c3s_3370_);
    leanh::lean_closure_set(v___f_3386_, 5, v_hyps_3371_);
    leanh::lean_closure_set(v___f_3386_, 6, v_target_3372_);
    leanh::lean_closure_set(v___f_3386_, 7, v_inst_3373_);
    leanh::lean_closure_set(v___f_3386_, 8, v_toBind_3374_);
    leanh::lean_closure_set(v___f_3386_, 9, v_a_3375_);
    leanh::lean_closure_set(v___f_3386_, 10, v_n_3376_);
    leanh::lean_closure_set(v___f_3386_, 11, v_f_3377_);
    leanh::lean_closure_set(v___f_3386_, 12, v_k_3378_);
    leanh::lean_closure_set(v___f_3386_, 13, v_fst_3384_);
    leanh::lean_closure_set(v___f_3386_, 14, v_revertArgsTypes_3379_);
    leanh::lean_closure_set(v___f_3386_, 15, v___x_3380_);
    leanh::lean_closure_set(v___f_3386_, 16, v___f_3381_);
    v___f_3387_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__16 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3387_, 0, v_inst_3373_);
    leanh::lean_closure_set(v___f_3387_, 1, v_toBind_3374_);
    leanh::lean_closure_set(v___f_3387_, 2, v___f_3386_);
    v___x_3388_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___closed__0;
    v_sz_3389_ = lean_array_size(v_revertArgs_3369_);
    v___x_3390_ = 0usize;
    v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3382_,
        v___x_3388_,
        v_sz_3389_,
        v___x_3390_,
        v_revertArgs_3369_,
    );
    v___x_3392_ = leanh::lean_apply_2(v_inst_3373_, leanh::lean_box(0), v___x_3391_);
    v___x_3393_ = leanh::lean_apply_4(
        v_toBind_3374_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3392_,
        v___f_3387_,
    );
    return v___x_3393_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3394_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_toApplicative_3395_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_revertArgs_3396_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_3397_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_hyps_3398_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_target_3399_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_3400_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_toBind_3401_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_3402_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_n_3403_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_f_3404_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_k_3405_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_revertArgsTypes_3406_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___x_3407_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_3408_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_3409_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_____x_3410_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3411_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17(
        v_u_3394_,
        v_toApplicative_3395_,
        v_revertArgs_3396_,
        v_00_u03c3s_3397_,
        v_hyps_3398_,
        v_target_3399_,
        v_inst_3400_,
        v_toBind_3401_,
        v_a_3402_,
        v_n_3403_,
        v_f_3404_,
        v_k_3405_,
        v_revertArgsTypes_3406_,
        v___x_3407_,
        v___f_3408_,
        v___x_3409_,
        v_____x_3410_,
    );
    return v_res_3411_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18(
    mut v_inst_3412_: *mut leanh::LeanObject,
    mut v_inst_3413_: *mut leanh::LeanObject,
    mut v___f_3414_: *mut leanh::LeanObject,
    mut v_toBind_3415_: *mut leanh::LeanObject,
    mut v___f_3416_: *mut leanh::LeanObject,
    mut v_declInfos_3417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3418_: u8 = 0;
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = 0;
    v___x_3419_ = l_Lean_Meta_withLocalDeclsDND___redArg(
        v_inst_3412_,
        v_inst_3413_,
        v_declInfos_3417_,
        v___f_3414_,
        v___x_3418_,
    );
    v___x_3420_ = leanh::lean_apply_4(
        v_toBind_3415_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3419_,
        v___f_3416_,
    );
    return v___x_3420_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(
    mut v_u_3421_: *mut leanh::LeanObject,
    mut v_toApplicative_3422_: *mut leanh::LeanObject,
    mut v_revertArgs_3423_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3424_: *mut leanh::LeanObject,
    mut v_hyps_3425_: *mut leanh::LeanObject,
    mut v_target_3426_: *mut leanh::LeanObject,
    mut v_inst_3427_: *mut leanh::LeanObject,
    mut v_toBind_3428_: *mut leanh::LeanObject,
    mut v_a_3429_: *mut leanh::LeanObject,
    mut v_n_3430_: *mut leanh::LeanObject,
    mut v_f_3431_: *mut leanh::LeanObject,
    mut v_k_3432_: *mut leanh::LeanObject,
    mut v___x_3433_: *mut leanh::LeanObject,
    mut v___f_3434_: *mut leanh::LeanObject,
    mut v___x_3435_: *mut leanh::LeanObject,
    mut v_inst_3436_: *mut leanh::LeanObject,
    mut v_inst_3437_: *mut leanh::LeanObject,
    mut v___f_3438_: *mut leanh::LeanObject,
    mut v___f_3439_: *mut leanh::LeanObject,
    mut v_revertArgsTypes_3440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___x_3433_);
    leanh::lean_inc_ref(v_revertArgsTypes_3440_);
    leanh::lean_inc_n(v_toBind_3428_, 2);
    v___f_3441_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__17___boxed
            as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_3441_, 0, v_u_3421_);
    leanh::lean_closure_set(v___f_3441_, 1, v_toApplicative_3422_);
    leanh::lean_closure_set(v___f_3441_, 2, v_revertArgs_3423_);
    leanh::lean_closure_set(v___f_3441_, 3, v_00_u03c3s_3424_);
    leanh::lean_closure_set(v___f_3441_, 4, v_hyps_3425_);
    leanh::lean_closure_set(v___f_3441_, 5, v_target_3426_);
    leanh::lean_closure_set(v___f_3441_, 6, v_inst_3427_);
    leanh::lean_closure_set(v___f_3441_, 7, v_toBind_3428_);
    leanh::lean_closure_set(v___f_3441_, 8, v_a_3429_);
    leanh::lean_closure_set(v___f_3441_, 9, v_n_3430_);
    leanh::lean_closure_set(v___f_3441_, 10, v_f_3431_);
    leanh::lean_closure_set(v___f_3441_, 11, v_k_3432_);
    leanh::lean_closure_set(v___f_3441_, 12, v_revertArgsTypes_3440_);
    leanh::lean_closure_set(v___f_3441_, 13, v___x_3433_);
    leanh::lean_closure_set(v___f_3441_, 14, v___f_3434_);
    leanh::lean_closure_set(v___f_3441_, 15, v___x_3435_);
    leanh::lean_inc_ref(v_inst_3437_);
    v___f_3442_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__18 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_3442_, 0, v_inst_3436_);
    leanh::lean_closure_set(v___f_3442_, 1, v_inst_3437_);
    leanh::lean_closure_set(v___f_3442_, 2, v___f_3438_);
    leanh::lean_closure_set(v___f_3442_, 3, v_toBind_3428_);
    leanh::lean_closure_set(v___f_3442_, 4, v___f_3441_);
    v___x_3443_ = lean_array_get_size(v_revertArgsTypes_3440_);
    v___x_3444_ = lean_mk_empty_array_with_capacity(v___x_3443_);
    v___x_3445_ = l_Array_mapFinIdxM_map___redArg(
        v_inst_3437_,
        v_revertArgsTypes_3440_,
        v___f_3439_,
        v___x_3443_,
        v___x_3433_,
        v___x_3444_,
    );
    v___x_3446_ = leanh::lean_apply_4(
        v_toBind_3428_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3445_,
        v___f_3442_,
    );
    return v___x_3446_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3447_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_toApplicative_3448_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_revertArgs_3449_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_3450_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_hyps_3451_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_target_3452_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_inst_3453_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_toBind_3454_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_3455_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_n_3456_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_f_3457_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_k_3458_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_3459_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_3460_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_3461_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_3462_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_inst_3463_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_3464_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___f_3465_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_revertArgsTypes_3466_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19(
        v_u_3447_,
        v_toApplicative_3448_,
        v_revertArgs_3449_,
        v_00_u03c3s_3450_,
        v_hyps_3451_,
        v_target_3452_,
        v_inst_3453_,
        v_toBind_3454_,
        v_a_3455_,
        v_n_3456_,
        v_f_3457_,
        v_k_3458_,
        v___x_3459_,
        v___f_3460_,
        v___x_3461_,
        v_inst_3462_,
        v_inst_3463_,
        v___f_3464_,
        v___f_3465_,
        v_revertArgsTypes_3466_,
    );
    return v_res_3467_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(
    mut v_inst_3469_: *mut leanh::LeanObject,
    mut v_inst_3470_: *mut leanh::LeanObject,
    mut v_u_3471_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3472_: *mut leanh::LeanObject,
    mut v_hypName_3473_: *mut leanh::LeanObject,
    mut v_hyps_3474_: *mut leanh::LeanObject,
    mut v___x_3475_: u8,
    mut v___f_3476_: *mut leanh::LeanObject,
    mut v_revertArgs_3477_: *mut leanh::LeanObject,
    mut v___f_3478_: *mut leanh::LeanObject,
    mut v_target_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
    mut v_n_3481_: *mut leanh::LeanObject,
    mut v_f_3482_: *mut leanh::LeanObject,
    mut v_k_3483_: *mut leanh::LeanObject,
    mut v___x_3484_: *mut leanh::LeanObject,
    mut v___f_3485_: *mut leanh::LeanObject,
    mut v_inst_3486_: *mut leanh::LeanObject,
    mut v_____r_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_toFunctor_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v___f_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3535_: usize = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v_unused_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_unused_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_3488_ = leanh::lean_ctor_get(v_inst_3469_, 0);
                leanh::lean_inc_ref(v_toApplicative_3488_);
                v_toBind_3489_ = leanh::lean_ctor_get(v_inst_3469_, 1);
                leanh::lean_inc(v_toBind_3489_);
                v___x_3490_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1,
                );
                v_toApplicative_3491_ = leanh::lean_ctor_get(v___x_3490_, 0);
                v_toFunctor_3492_ = leanh::lean_ctor_get(v_toApplicative_3491_, 0);
                v_toSeq_3493_ = leanh::lean_ctor_get(v_toApplicative_3491_, 2);
                v_toSeqLeft_3494_ = leanh::lean_ctor_get(v_toApplicative_3491_, 3);
                v_toSeqRight_3495_ = leanh::lean_ctor_get(v_toApplicative_3491_, 4);
                v___f_3496_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2;
                v___f_3497_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3492_, 2);
                v___f_3498_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3498_, 0, v_toFunctor_3492_);
                v___f_3499_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3499_, 0, v_toFunctor_3492_);
                v___x_3500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3500_, 0, v___f_3498_);
                leanh::lean_ctor_set(v___x_3500_, 1, v___f_3499_);
                leanh::lean_inc(v_toSeqRight_3495_);
                v___f_3501_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3501_, 0, v_toSeqRight_3495_);
                leanh::lean_inc(v_toSeqLeft_3494_);
                v___f_3502_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3502_, 0, v_toSeqLeft_3494_);
                leanh::lean_inc(v_toSeq_3493_);
                v___f_3503_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3503_, 0, v_toSeq_3493_);
                v___x_3504_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3504_, 0, v___x_3500_);
                leanh::lean_ctor_set(v___x_3504_, 1, v___f_3496_);
                leanh::lean_ctor_set(v___x_3504_, 2, v___f_3503_);
                leanh::lean_ctor_set(v___x_3504_, 3, v___f_3502_);
                leanh::lean_ctor_set(v___x_3504_, 4, v___f_3501_);
                v___x_3505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                leanh::lean_ctor_set(v___x_3505_, 1, v___f_3497_);
                v___x_3506_ = l_StateRefT_x27_instMonad___redArg(v___x_3505_);
                v_toApplicative_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                v_isSharedCheck_3544_ = (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                if v_isSharedCheck_3544_ == 0 {
                    v_unused_3545_ = leanh::lean_ctor_get(v___x_3506_, 1);
                    leanh::lean_dec(v_unused_3545_);
                    v___x_3509_ = v___x_3506_;
                    v_isShared_3510_ = v_isSharedCheck_3544_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3507_);
                    leanh::lean_dec(v___x_3506_);
                    v___x_3509_ = leanh::lean_box(0);
                    v_isShared_3510_ = v_isSharedCheck_3544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3511_ = leanh::lean_ctor_get(v_toApplicative_3507_, 0);
                v_toSeq_3512_ = leanh::lean_ctor_get(v_toApplicative_3507_, 2);
                v_toSeqLeft_3513_ = leanh::lean_ctor_get(v_toApplicative_3507_, 3);
                v_toSeqRight_3514_ = leanh::lean_ctor_get(v_toApplicative_3507_, 4);
                v_isSharedCheck_3542_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3507_)) as u8;
                if v_isSharedCheck_3542_ == 0 {
                    v_unused_3543_ = leanh::lean_ctor_get(v_toApplicative_3507_, 1);
                    leanh::lean_dec(v_unused_3543_);
                    v___x_3516_ = v_toApplicative_3507_;
                    v_isShared_3517_ = v_isSharedCheck_3542_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3514_);
                    leanh::lean_inc(v_toSeqLeft_3513_);
                    leanh::lean_inc(v_toSeq_3512_);
                    leanh::lean_inc(v_toFunctor_3511_);
                    leanh::lean_dec(v_toApplicative_3507_);
                    v___x_3516_ = leanh::lean_box(0);
                    v_isShared_3517_ = v_isSharedCheck_3542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_toBind_3489_, 2);
                leanh::lean_inc_n(v_inst_3470_, 2);
                leanh::lean_inc_ref_n(v_toApplicative_3488_, 2);
                v___f_3518_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6
                        as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___f_3518_, 0, v_toApplicative_3488_);
                leanh::lean_closure_set(v___f_3518_, 1, v_inst_3470_);
                leanh::lean_closure_set(v___f_3518_, 2, v_toBind_3489_);
                v___x_3519_ = leanh::lean_box((v___x_3475_) as usize);
                leanh::lean_inc_ref(v_inst_3469_);
                leanh::lean_inc_ref(v_revertArgs_3477_);
                leanh::lean_inc_ref(v_hyps_3474_);
                leanh::lean_inc_ref(v_00_u03c3s_3472_);
                leanh::lean_inc(v_u_3471_);
                v___f_3520_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__11___boxed
                        as *mut core::ffi::c_void,
                    13,
                    12,
                );
                leanh::lean_closure_set(v___f_3520_, 0, v_u_3471_);
                leanh::lean_closure_set(v___f_3520_, 1, v_00_u03c3s_3472_);
                leanh::lean_closure_set(v___f_3520_, 2, v_hypName_3473_);
                leanh::lean_closure_set(v___f_3520_, 3, v_toApplicative_3488_);
                leanh::lean_closure_set(v___f_3520_, 4, v_hyps_3474_);
                leanh::lean_closure_set(v___f_3520_, 5, v___x_3519_);
                leanh::lean_closure_set(v___f_3520_, 6, v_inst_3470_);
                leanh::lean_closure_set(v___f_3520_, 7, v_toBind_3489_);
                leanh::lean_closure_set(v___f_3520_, 8, v___f_3476_);
                leanh::lean_closure_set(v___f_3520_, 9, v_revertArgs_3477_);
                leanh::lean_closure_set(v___f_3520_, 10, v_inst_3469_);
                leanh::lean_closure_set(v___f_3520_, 11, v___f_3478_);
                v___f_3521_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4;
                v___f_3522_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_3511_);
                v___f_3523_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3523_, 0, v_toFunctor_3511_);
                v___f_3524_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3524_, 0, v_toFunctor_3511_);
                v___x_3525_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3525_, 0, v___f_3523_);
                leanh::lean_ctor_set(v___x_3525_, 1, v___f_3524_);
                v___f_3526_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3526_, 0, v_toSeqRight_3514_);
                v___f_3527_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3527_, 0, v_toSeqLeft_3513_);
                v___f_3528_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3528_, 0, v_toSeq_3512_);
                if v_isShared_3517_ == 0 {
                    leanh::lean_ctor_set(v___x_3516_, 4, v___f_3526_);
                    leanh::lean_ctor_set(v___x_3516_, 3, v___f_3527_);
                    leanh::lean_ctor_set(v___x_3516_, 2, v___f_3528_);
                    leanh::lean_ctor_set(v___x_3516_, 1, v___f_3521_);
                    leanh::lean_ctor_set(v___x_3516_, 0, v___x_3525_);
                    v___x_3530_ = v___x_3516_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 1, v___f_3521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 2, v___f_3528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 3, v___f_3527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 4, v___f_3526_);
                    v___x_3530_ = v_reuseFailAlloc_3541_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3510_ == 0 {
                    leanh::lean_ctor_set(v___x_3509_, 1, v___f_3522_);
                    leanh::lean_ctor_set(v___x_3509_, 0, v___x_3530_);
                    v___x_3532_ = v___x_3509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___f_3522_);
                    v___x_3532_ = v_reuseFailAlloc_3540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_3532_);
                leanh::lean_inc(v_toBind_3489_);
                leanh::lean_inc(v_inst_3470_);
                leanh::lean_inc_ref(v_revertArgs_3477_);
                v___f_3533_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__19___boxed
                        as *mut core::ffi::c_void,
                    20,
                    19,
                );
                leanh::lean_closure_set(v___f_3533_, 0, v_u_3471_);
                leanh::lean_closure_set(v___f_3533_, 1, v_toApplicative_3488_);
                leanh::lean_closure_set(v___f_3533_, 2, v_revertArgs_3477_);
                leanh::lean_closure_set(v___f_3533_, 3, v_00_u03c3s_3472_);
                leanh::lean_closure_set(v___f_3533_, 4, v_hyps_3474_);
                leanh::lean_closure_set(v___f_3533_, 5, v_target_3479_);
                leanh::lean_closure_set(v___f_3533_, 6, v_inst_3470_);
                leanh::lean_closure_set(v___f_3533_, 7, v_toBind_3489_);
                leanh::lean_closure_set(v___f_3533_, 8, v_a_3480_);
                leanh::lean_closure_set(v___f_3533_, 9, v_n_3481_);
                leanh::lean_closure_set(v___f_3533_, 10, v_f_3482_);
                leanh::lean_closure_set(v___f_3533_, 11, v_k_3483_);
                leanh::lean_closure_set(v___f_3533_, 12, v___x_3484_);
                leanh::lean_closure_set(v___f_3533_, 13, v___f_3485_);
                leanh::lean_closure_set(v___f_3533_, 14, v___x_3532_);
                leanh::lean_closure_set(v___f_3533_, 15, v_inst_3486_);
                leanh::lean_closure_set(v___f_3533_, 16, v_inst_3469_);
                leanh::lean_closure_set(v___f_3533_, 17, v___f_3520_);
                leanh::lean_closure_set(v___f_3533_, 18, v___f_3518_);
                v___x_3534_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___closed__0;
                v_sz_3535_ = lean_array_size(v_revertArgs_3477_);
                v___x_3536_ = 0usize;
                v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3532_,
                    v___x_3534_,
                    v_sz_3535_,
                    v___x_3536_,
                    v_revertArgs_3477_,
                );
                v___x_3538_ = leanh::lean_apply_2(
                    v_inst_3470_,
                    leanh::lean_box(0),
                    v___x_3537_,
                );
                v___x_3539_ = leanh::lean_apply_4(
                    v_toBind_3489_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3538_,
                    v___f_3533_,
                );
                return v___x_3539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_3546_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_3547_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_u_3548_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_3549_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_hypName_3550_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_hyps_3551_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3552_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_3553_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_revertArgs_3554_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_3555_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_target_3556_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_3557_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_n_3558_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_f_3559_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_k_3560_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_3561_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_3562_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_inst_3563_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_____r_3564_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___x_1542__boxed_3565_: u8 = 0;
    let mut v_res_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1542__boxed_3565_ = (leanh::lean_unbox(v___x_3552_) as u8);
    v_res_3566_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(
        v_inst_3546_,
        v_inst_3547_,
        v_u_3548_,
        v_00_u03c3s_3549_,
        v_hypName_3550_,
        v_hyps_3551_,
        v___x_1542__boxed_3565_,
        v___f_3553_,
        v_revertArgs_3554_,
        v___f_3555_,
        v_target_3556_,
        v_a_3557_,
        v_n_3558_,
        v_f_3559_,
        v_k_3560_,
        v___x_3561_,
        v___f_3562_,
        v_inst_3563_,
        v_____r_3564_,
    );
    return v_res_3566_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21(
    mut v___f_3567_: *mut leanh::LeanObject,
    mut v_____r_3568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ = leanh::lean_apply_1(v___f_3567_, v_____r_3568_);
    return v___x_3569_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3574_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__2;
    v___x_3575_ = l_Lean_stringToMessageData(v___x_3574_);
    return v___x_3575_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3577_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__4;
    v___x_3578_ = l_Lean_stringToMessageData(v___x_3577_);
    return v___x_3578_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__6;
    v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(
    mut v_inst_3582_: *mut leanh::LeanObject,
    mut v_inst_3583_: *mut leanh::LeanObject,
    mut v_inst_3584_: *mut leanh::LeanObject,
    mut v_goal_3585_: *mut leanh::LeanObject,
    mut v_n_3586_: *mut leanh::LeanObject,
    mut v_hypName_3587_: *mut leanh::LeanObject,
    mut v_k_3588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: u8 = 0;
    let mut v_u_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_T_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_revertArgs_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v_toBind_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v_toFunctor_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___f_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_unused_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut v_unused_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3589_ = leanh::lean_unsigned_to_nat(0);
                v___x_3590_ = lean_nat_dec_eq(v_n_3586_, v___x_3589_);
                if v___x_3590_ == 0 {
                    v_u_3591_ = leanh::lean_ctor_get(v_goal_3585_, 0);
                    leanh::lean_inc_n(v_u_3591_, 3);
                    v_00_u03c3s_3592_ = leanh::lean_ctor_get(v_goal_3585_, 1);
                    leanh::lean_inc_ref_n(v_00_u03c3s_3592_, 2);
                    v_hyps_3593_ = leanh::lean_ctor_get(v_goal_3585_, 2);
                    leanh::lean_inc_ref_n(v_hyps_3593_, 2);
                    v_target_3594_ = leanh::lean_ctor_get(v_goal_3585_, 3);
                    leanh::lean_inc_ref_n(v_target_3594_, 2);
                    leanh::lean_dec_ref(v_goal_3585_);
                    leanh::lean_inc_n(v_inst_3584_, 2);
                    v___f_3595_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__0
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_3595_, 0, v_inst_3584_);
                    leanh::lean_inc_n(v_hypName_3587_, 2);
                    v___f_3596_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___f_3596_, 0, v_hypName_3587_);
                    v___f_3597_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__0;
                    v___f_3598_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__3
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___f_3598_, 0, v_u_3591_);
                    v_T_3599_ = l_Lean_Expr_consumeMData(v_target_3594_);
                    v_f_3600_ = l_Lean_Expr_getAppFn(v_T_3599_);
                    v___x_3601_ = l_Lean_Expr_getAppNumArgs(v_T_3599_);
                    v___x_3602_ = lean_mk_empty_array_with_capacity(v___x_3601_);
                    leanh::lean_dec(v___x_3601_);
                    leanh::lean_inc_ref(v_T_3599_);
                    v_a_3603_ =
                        l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_3599_, v___x_3602_);
                    leanh::lean_inc_n(v_n_3586_, 2);
                    leanh::lean_inc_ref_n(v_a_3603_, 2);
                    v___x_3604_ = l_Array_toSubarray___redArg(v_a_3603_, v___x_3589_, v_n_3586_);
                    v___x_3605_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1;
                    v___x_3606_ =
                        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                            v___f_3597_,
                            v___x_3604_,
                            v___x_3605_,
                        );
                    v_revertArgs_3607_ = l_Array_reverse___redArg(v___x_3606_);
                    v___x_3608_ = leanh::lean_box((v___x_3590_) as usize);
                    leanh::lean_inc_ref(v_inst_3583_);
                    leanh::lean_inc_ref(v___f_3598_);
                    leanh::lean_inc(v_k_3588_);
                    leanh::lean_inc_ref(v_f_3600_);
                    leanh::lean_inc_ref(v___f_3595_);
                    leanh::lean_inc_ref(v_revertArgs_3607_);
                    leanh::lean_inc_ref(v___f_3596_);
                    leanh::lean_inc_ref(v_inst_3582_);
                    v___f_3609_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20___boxed
                            as *mut core::ffi::c_void,
                        19,
                        18,
                    );
                    leanh::lean_closure_set(v___f_3609_, 0, v_inst_3582_);
                    leanh::lean_closure_set(v___f_3609_, 1, v_inst_3584_);
                    leanh::lean_closure_set(v___f_3609_, 2, v_u_3591_);
                    leanh::lean_closure_set(v___f_3609_, 3, v_00_u03c3s_3592_);
                    leanh::lean_closure_set(v___f_3609_, 4, v_hypName_3587_);
                    leanh::lean_closure_set(v___f_3609_, 5, v_hyps_3593_);
                    leanh::lean_closure_set(v___f_3609_, 6, v___x_3608_);
                    leanh::lean_closure_set(v___f_3609_, 7, v___f_3596_);
                    leanh::lean_closure_set(v___f_3609_, 8, v_revertArgs_3607_);
                    leanh::lean_closure_set(v___f_3609_, 9, v___f_3595_);
                    leanh::lean_closure_set(v___f_3609_, 10, v_target_3594_);
                    leanh::lean_closure_set(v___f_3609_, 11, v_a_3603_);
                    leanh::lean_closure_set(v___f_3609_, 12, v_n_3586_);
                    leanh::lean_closure_set(v___f_3609_, 13, v_f_3600_);
                    leanh::lean_closure_set(v___f_3609_, 14, v_k_3588_);
                    leanh::lean_closure_set(v___f_3609_, 15, v___x_3589_);
                    leanh::lean_closure_set(v___f_3609_, 16, v___f_3598_);
                    leanh::lean_closure_set(v___f_3609_, 17, v_inst_3583_);
                    v___x_3610_ = lean_array_get_size(v_revertArgs_3607_);
                    v___x_3611_ = lean_nat_dec_eq(v___x_3610_, v_n_3586_);
                    if v___x_3611_ == 0 {
                        leanh::lean_dec_ref(v_revertArgs_3607_);
                        leanh::lean_dec_ref(v_a_3603_);
                        leanh::lean_dec_ref(v_f_3600_);
                        leanh::lean_dec_ref(v___f_3598_);
                        leanh::lean_dec_ref(v___f_3596_);
                        leanh::lean_dec_ref(v___f_3595_);
                        leanh::lean_dec_ref(v_target_3594_);
                        leanh::lean_dec_ref(v_hyps_3593_);
                        leanh::lean_dec_ref(v_00_u03c3s_3592_);
                        leanh::lean_dec(v_u_3591_);
                        leanh::lean_dec(v_k_3588_);
                        leanh::lean_dec(v_hypName_3587_);
                        leanh::lean_dec_ref(v_inst_3583_);
                        v_toBind_3612_ = leanh::lean_ctor_get(v_inst_3582_, 1);
                        v_isSharedCheck_3689_ =
                            (!leanh::lean_is_exclusive(v_inst_3582_)) as u8;
                        if v_isSharedCheck_3689_ == 0 {
                            v_unused_3690_ = leanh::lean_ctor_get(v_inst_3582_, 0);
                            leanh::lean_dec(v_unused_3690_);
                            v___x_3614_ = v_inst_3582_;
                            v_isShared_3615_ = v_isSharedCheck_3689_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_toBind_3612_);
                            leanh::lean_dec(v_inst_3582_);
                            v___x_3614_ = leanh::lean_box(0);
                            v_isShared_3615_ = v_isSharedCheck_3689_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_3609_);
                        leanh::lean_dec_ref(v_T_3599_);
                        v___x_3691_ = leanh::lean_box(0);
                        v___x_3692_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__20(
                                v_inst_3582_,
                                v_inst_3584_,
                                v_u_3591_,
                                v_00_u03c3s_3592_,
                                v_hypName_3587_,
                                v_hyps_3593_,
                                v___x_3590_,
                                v___f_3596_,
                                v_revertArgs_3607_,
                                v___f_3595_,
                                v_target_3594_,
                                v_a_3603_,
                                v_n_3586_,
                                v_f_3600_,
                                v_k_3588_,
                                v___x_3589_,
                                v___f_3598_,
                                v_inst_3583_,
                                v___x_3691_,
                            );
                        return v___x_3692_;
                    }
                } else {
                    leanh::lean_dec(v_hypName_3587_);
                    leanh::lean_dec(v_n_3586_);
                    leanh::lean_dec(v_inst_3584_);
                    leanh::lean_dec_ref(v_inst_3583_);
                    leanh::lean_dec_ref(v_inst_3582_);
                    v___x_3693_ = leanh::lean_apply_1(v_k_3588_, v_goal_3585_);
                    return v___x_3693_;
                }
            }
            1 => {
                v___x_3616_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1,
                );
                v_toApplicative_3617_ = leanh::lean_ctor_get(v___x_3616_, 0);
                v_toFunctor_3618_ = leanh::lean_ctor_get(v_toApplicative_3617_, 0);
                v_toSeq_3619_ = leanh::lean_ctor_get(v_toApplicative_3617_, 2);
                v_toSeqLeft_3620_ = leanh::lean_ctor_get(v_toApplicative_3617_, 3);
                v_toSeqRight_3621_ = leanh::lean_ctor_get(v_toApplicative_3617_, 4);
                v___f_3622_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2;
                v___f_3623_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3618_, 2);
                v___f_3624_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3624_, 0, v_toFunctor_3618_);
                v___f_3625_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3625_, 0, v_toFunctor_3618_);
                v___x_3626_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3626_, 0, v___f_3624_);
                leanh::lean_ctor_set(v___x_3626_, 1, v___f_3625_);
                leanh::lean_inc(v_toSeqRight_3621_);
                v___f_3627_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3627_, 0, v_toSeqRight_3621_);
                leanh::lean_inc(v_toSeqLeft_3620_);
                v___f_3628_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3628_, 0, v_toSeqLeft_3620_);
                leanh::lean_inc(v_toSeq_3619_);
                v___f_3629_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3629_, 0, v_toSeq_3619_);
                v___x_3630_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3630_, 0, v___x_3626_);
                leanh::lean_ctor_set(v___x_3630_, 1, v___f_3622_);
                leanh::lean_ctor_set(v___x_3630_, 2, v___f_3629_);
                leanh::lean_ctor_set(v___x_3630_, 3, v___f_3628_);
                leanh::lean_ctor_set(v___x_3630_, 4, v___f_3627_);
                if v_isShared_3615_ == 0 {
                    leanh::lean_ctor_set(v___x_3614_, 1, v___f_3623_);
                    leanh::lean_ctor_set(v___x_3614_, 0, v___x_3630_);
                    v___x_3632_ = v___x_3614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___f_3623_);
                    v___x_3632_ = v_reuseFailAlloc_3688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3633_ = l_StateRefT_x27_instMonad___redArg(v___x_3632_);
                v_toApplicative_3634_ = leanh::lean_ctor_get(v___x_3633_, 0);
                v_isSharedCheck_3686_ = (!leanh::lean_is_exclusive(v___x_3633_)) as u8;
                if v_isSharedCheck_3686_ == 0 {
                    v_unused_3687_ = leanh::lean_ctor_get(v___x_3633_, 1);
                    leanh::lean_dec(v_unused_3687_);
                    v___x_3636_ = v___x_3633_;
                    v_isShared_3637_ = v_isSharedCheck_3686_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3634_);
                    leanh::lean_dec(v___x_3633_);
                    v___x_3636_ = leanh::lean_box(0);
                    v_isShared_3637_ = v_isSharedCheck_3686_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_toFunctor_3638_ = leanh::lean_ctor_get(v_toApplicative_3634_, 0);
                v_toSeq_3639_ = leanh::lean_ctor_get(v_toApplicative_3634_, 2);
                v_toSeqLeft_3640_ = leanh::lean_ctor_get(v_toApplicative_3634_, 3);
                v_toSeqRight_3641_ = leanh::lean_ctor_get(v_toApplicative_3634_, 4);
                v_isSharedCheck_3684_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3634_)) as u8;
                if v_isSharedCheck_3684_ == 0 {
                    v_unused_3685_ = leanh::lean_ctor_get(v_toApplicative_3634_, 1);
                    leanh::lean_dec(v_unused_3685_);
                    v___x_3643_ = v_toApplicative_3634_;
                    v_isShared_3644_ = v_isSharedCheck_3684_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3641_);
                    leanh::lean_inc(v_toSeqLeft_3640_);
                    leanh::lean_inc(v_toSeq_3639_);
                    leanh::lean_inc(v_toFunctor_3638_);
                    leanh::lean_dec(v_toApplicative_3634_);
                    v___x_3643_ = leanh::lean_box(0);
                    v_isShared_3644_ = v_isSharedCheck_3684_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___f_3645_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4;
                v___f_3646_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_3638_);
                v___f_3647_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3647_, 0, v_toFunctor_3638_);
                v___f_3648_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3648_, 0, v_toFunctor_3638_);
                v___x_3649_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3649_, 0, v___f_3647_);
                leanh::lean_ctor_set(v___x_3649_, 1, v___f_3648_);
                v___f_3650_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3650_, 0, v_toSeqRight_3641_);
                v___f_3651_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3651_, 0, v_toSeqLeft_3640_);
                v___f_3652_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3652_, 0, v_toSeq_3639_);
                if v_isShared_3644_ == 0 {
                    leanh::lean_ctor_set(v___x_3643_, 4, v___f_3650_);
                    leanh::lean_ctor_set(v___x_3643_, 3, v___f_3651_);
                    leanh::lean_ctor_set(v___x_3643_, 2, v___f_3652_);
                    leanh::lean_ctor_set(v___x_3643_, 1, v___f_3645_);
                    leanh::lean_ctor_set(v___x_3643_, 0, v___x_3649_);
                    v___x_3654_ = v___x_3643_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___f_3645_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 2, v___f_3652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 3, v___f_3651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 4, v___f_3650_);
                    v___x_3654_ = v_reuseFailAlloc_3683_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3637_ == 0 {
                    leanh::lean_ctor_set(v___x_3636_, 1, v___f_3646_);
                    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3636_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___f_3646_);
                    v___x_3656_ = v_reuseFailAlloc_3682_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3657_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__11,
                );
                v___x_3658_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__17,
                );
                v_toMonadRef_3659_ = leanh::lean_ctor_get(v___x_3658_, 0);
                v___f_3660_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__21
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3660_, 0, v___f_3609_);
                v___x_3661_ = l_Lean_Meta_instAddMessageContextMetaM;
                leanh::lean_inc_ref(v___x_3656_);
                v___x_3662_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_3661_,
                    v___x_3656_,
                );
                leanh::lean_inc_ref(v_toMonadRef_3659_);
                v___x_3663_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3663_, 0, v___x_3657_);
                leanh::lean_ctor_set(v___x_3663_, 1, v_toMonadRef_3659_);
                leanh::lean_ctor_set(v___x_3663_, 2, v___x_3662_);
                v___x_3664_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3,
                );
                v___x_3665_ = l_Nat_reprFast(v_n_3586_);
                v___x_3666_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
                v___x_3667_ = l_Lean_MessageData_ofFormat(v___x_3666_);
                v___x_3668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3668_, 0, v___x_3664_);
                leanh::lean_ctor_set(v___x_3668_, 1, v___x_3667_);
                v___x_3669_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5,
                );
                v___x_3670_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3670_, 0, v___x_3668_);
                leanh::lean_ctor_set(v___x_3670_, 1, v___x_3669_);
                v___x_3671_ = l_Lean_MessageData_ofExpr(v_T_3599_);
                v___x_3672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3672_, 0, v___x_3670_);
                leanh::lean_ctor_set(v___x_3672_, 1, v___x_3671_);
                v___x_3673_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7,
                );
                v___x_3674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3674_, 0, v___x_3672_);
                leanh::lean_ctor_set(v___x_3674_, 1, v___x_3673_);
                v___x_3675_ = l_Nat_reprFast(v___x_3610_);
                v___x_3676_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3676_, 0, v___x_3675_);
                v___x_3677_ = l_Lean_MessageData_ofFormat(v___x_3676_);
                v___x_3678_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3678_, 0, v___x_3674_);
                leanh::lean_ctor_set(v___x_3678_, 1, v___x_3677_);
                v___x_3679_ = l_Lean_throwError___redArg(v___x_3656_, v___x_3663_, v___x_3678_);
                v___x_3680_ = leanh::lean_apply_2(
                    v_inst_3584_,
                    leanh::lean_box(0),
                    v___x_3679_,
                );
                v___x_3681_ = leanh::lean_apply_4(
                    v_toBind_3612_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3680_,
                    v___f_3660_,
                );
                return v___x_3681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN(
    mut v_m_3694_: *mut leanh::LeanObject,
    mut v_inst_3695_: *mut leanh::LeanObject,
    mut v_inst_3696_: *mut leanh::LeanObject,
    mut v_inst_3697_: *mut leanh::LeanObject,
    mut v_goal_3698_: *mut leanh::LeanObject,
    mut v_n_3699_: *mut leanh::LeanObject,
    mut v_hypName_3700_: *mut leanh::LeanObject,
    mut v_k_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg(
        v_inst_3695_,
        v_inst_3696_,
        v_inst_3697_,
        v_goal_3698_,
        v_n_3699_,
        v_hypName_3700_,
        v_k_3701_,
    );
    return v___x_3702_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = leanh::lean_box(0);
    v___x_3704_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3705_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3705_, 0, v___x_3704_);
    leanh::lean_ctor_set(v___x_3705_, 1, v___x_3703_);
    return v___x_3705_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3707_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___closed__0);
    v___x_3708_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3708_, 0, v___x_3707_);
    return v___x_3708_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg___boxed(
    mut v___y_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
    return v_res_3710_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(
    mut v_00_u03b1_3711_: *mut leanh::LeanObject,
    mut v___y_3712_: *mut leanh::LeanObject,
    mut v___y_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
    return v___x_3721_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___boxed(
    mut v_00_u03b1_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0(v_00_u03b1_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
    leanh::lean_dec(v___y_3730_);
    leanh::lean_dec_ref(v___y_3729_);
    leanh::lean_dec(v___y_3728_);
    leanh::lean_dec_ref(v___y_3727_);
    leanh::lean_dec(v___y_3726_);
    leanh::lean_dec_ref(v___y_3725_);
    leanh::lean_dec(v___y_3724_);
    leanh::lean_dec_ref(v___y_3723_);
    return v_res_3732_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(
    mut v_x_3733_: *mut leanh::LeanObject,
    mut v___y_3734_: *mut leanh::LeanObject,
    mut v___y_3735_: *mut leanh::LeanObject,
    mut v___y_3736_: *mut leanh::LeanObject,
    mut v___y_3737_: *mut leanh::LeanObject,
    mut v___y_3738_: *mut leanh::LeanObject,
    mut v___y_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
    mut v___y_3741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3737_);
    leanh::lean_inc_ref(v___y_3736_);
    leanh::lean_inc(v___y_3735_);
    leanh::lean_inc_ref(v___y_3734_);
    v___x_3743_ = leanh::lean_apply_9(
        v_x_3733_,
        v___y_3734_,
        v___y_3735_,
        v___y_3736_,
        v___y_3737_,
        v___y_3738_,
        v___y_3739_,
        v___y_3740_,
        v___y_3741_,
        leanh::lean_box(0),
    );
    return v___x_3743_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed(
    mut v_x_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0(v_x_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    leanh::lean_dec(v___y_3746_);
    leanh::lean_dec_ref(v___y_3745_);
    return v_res_3754_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(
    mut v_mvarId_3755_: *mut leanh::LeanObject,
    mut v_x_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3760_);
                leanh::lean_inc_ref(v___y_3759_);
                leanh::lean_inc(v___y_3758_);
                leanh::lean_inc_ref(v___y_3757_);
                v___f_3766_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_3766_, 0, v_x_3756_);
                leanh::lean_closure_set(v___f_3766_, 1, v___y_3757_);
                leanh::lean_closure_set(v___f_3766_, 2, v___y_3758_);
                leanh::lean_closure_set(v___f_3766_, 3, v___y_3759_);
                leanh::lean_closure_set(v___f_3766_, 4, v___y_3760_);
                v___x_3767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3755_,
                    v___f_3766_,
                    v___y_3761_,
                    v___y_3762_,
                    v___y_3763_,
                    v___y_3764_,
                );
                if leanh::lean_obj_tag(v___x_3767_) == 0 {
                    return v___x_3767_;
                } else {
                    v_a_3768_ = leanh::lean_ctor_get(v___x_3767_, 0);
                    v_isSharedCheck_3775_ = (!leanh::lean_is_exclusive(v___x_3767_)) as u8;
                    if v_isSharedCheck_3775_ == 0 {
                        v___x_3770_ = v___x_3767_;
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3768_);
                        leanh::lean_dec(v___x_3767_);
                        v___x_3770_ = leanh::lean_box(0);
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3771_ == 0 {
                    v___x_3773_ = v___x_3770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
                    v___x_3773_ = v_reuseFailAlloc_3774_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg___boxed(
    mut v_mvarId_3776_: *mut leanh::LeanObject,
    mut v_x_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_3776_, v_x_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
    leanh::lean_dec(v___y_3785_);
    leanh::lean_dec_ref(v___y_3784_);
    leanh::lean_dec(v___y_3783_);
    leanh::lean_dec_ref(v___y_3782_);
    leanh::lean_dec(v___y_3781_);
    leanh::lean_dec_ref(v___y_3780_);
    leanh::lean_dec(v___y_3779_);
    leanh::lean_dec_ref(v___y_3778_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(
    mut v_00_u03b1_3788_: *mut leanh::LeanObject,
    mut v_mvarId_3789_: *mut leanh::LeanObject,
    mut v_x_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_mvarId_3789_, v_x_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
    return v___x_3800_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___boxed(
    mut v_00_u03b1_3801_: *mut leanh::LeanObject,
    mut v_mvarId_3802_: *mut leanh::LeanObject,
    mut v_x_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
    mut v___y_3806_: *mut leanh::LeanObject,
    mut v___y_3807_: *mut leanh::LeanObject,
    mut v___y_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3(
            v_00_u03b1_3801_,
            v_mvarId_3802_,
            v_x_3803_,
            v___y_3804_,
            v___y_3805_,
            v___y_3806_,
            v___y_3807_,
            v___y_3808_,
            v___y_3809_,
            v___y_3810_,
            v___y_3811_,
        );
    leanh::lean_dec(v___y_3811_);
    leanh::lean_dec_ref(v___y_3810_);
    leanh::lean_dec(v___y_3809_);
    leanh::lean_dec_ref(v___y_3808_);
    leanh::lean_dec(v___y_3807_);
    leanh::lean_dec_ref(v___y_3806_);
    leanh::lean_dec(v___y_3805_);
    leanh::lean_dec_ref(v___y_3804_);
    return v_res_3813_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(
    mut v_val_3814_: *mut leanh::LeanObject,
    mut v_newGoal_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3825_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_3815_);
                v___x_3826_ = leanh::lean_box(0);
                v___x_3827_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3825_,
                    v___x_3826_,
                    v___y_3820_,
                    v___y_3821_,
                    v___y_3822_,
                    v___y_3823_,
                );
                if leanh::lean_obj_tag(v___x_3827_) == 0 {
                    v_a_3828_ = leanh::lean_ctor_get(v___x_3827_, 0);
                    v_isSharedCheck_3839_ = (!leanh::lean_is_exclusive(v___x_3827_)) as u8;
                    if v_isSharedCheck_3839_ == 0 {
                        v___x_3830_ = v___x_3827_;
                        v_isShared_3831_ = v_isSharedCheck_3839_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3828_);
                        leanh::lean_dec(v___x_3827_);
                        v___x_3830_ = leanh::lean_box(0);
                        v_isShared_3831_ = v_isSharedCheck_3839_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3827_;
                }
            }
            1 => {
                v___x_3832_ = lean_st_ref_take(v_val_3814_);
                v___x_3833_ = l_Lean_Expr_mvarId_x21(v_a_3828_);
                v___x_3834_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3834_, 0, v___x_3833_);
                leanh::lean_ctor_set(v___x_3834_, 1, v___x_3832_);
                v___x_3835_ = lean_st_ref_set(v_val_3814_, v___x_3834_);
                if v_isShared_3831_ == 0 {
                    v___x_3837_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3828_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed(
    mut v_val_3840_: *mut leanh::LeanObject,
    mut v_newGoal_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
    mut v___y_3847_: *mut leanh::LeanObject,
    mut v___y_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
    mut v___y_3850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3851_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0(
        v_val_3840_,
        v_newGoal_3841_,
        v___y_3842_,
        v___y_3843_,
        v___y_3844_,
        v___y_3845_,
        v___y_3846_,
        v___y_3847_,
        v___y_3848_,
        v___y_3849_,
    );
    leanh::lean_dec(v___y_3849_);
    leanh::lean_dec_ref(v___y_3848_);
    leanh::lean_dec(v___y_3847_);
    leanh::lean_dec_ref(v___y_3846_);
    leanh::lean_dec(v___y_3845_);
    leanh::lean_dec_ref(v___y_3844_);
    leanh::lean_dec(v___y_3843_);
    leanh::lean_dec_ref(v___y_3842_);
    leanh::lean_dec(v_val_3840_);
    return v_res_3851_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(
    mut v_x_3852_: *mut leanh::LeanObject,
    mut v_x_3853_: *mut leanh::LeanObject,
    mut v_x_3854_: *mut leanh::LeanObject,
    mut v_x_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3860_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3856_ = leanh::lean_ctor_get(v_x_3852_, 0);
                v_vs_3857_ = leanh::lean_ctor_get(v_x_3852_, 1);
                v_isSharedCheck_3881_ = (!leanh::lean_is_exclusive(v_x_3852_)) as u8;
                if v_isSharedCheck_3881_ == 0 {
                    v___x_3859_ = v_x_3852_;
                    v_isShared_3860_ = v_isSharedCheck_3881_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3857_);
                    leanh::lean_inc(v_ks_3856_);
                    leanh::lean_dec(v_x_3852_);
                    v___x_3859_ = leanh::lean_box(0);
                    v_isShared_3860_ = v_isSharedCheck_3881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3861_ = lean_array_get_size(v_ks_3856_);
                v___x_3862_ = lean_nat_dec_lt(v_x_3853_, v___x_3861_);
                if v___x_3862_ == 0 {
                    leanh::lean_dec(v_x_3853_);
                    v___x_3863_ = lean_array_push(v_ks_3856_, v_x_3854_);
                    v___x_3864_ = lean_array_push(v_vs_3857_, v_x_3855_);
                    if v_isShared_3860_ == 0 {
                        leanh::lean_ctor_set(v___x_3859_, 1, v___x_3864_);
                        leanh::lean_ctor_set(v___x_3859_, 0, v___x_3863_);
                        v___x_3866_ = v___x_3859_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3867_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3863_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 1, v___x_3864_);
                        v___x_3866_ = v_reuseFailAlloc_3867_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3868_ = lean_array_fget_borrowed(v_ks_3856_, v_x_3853_);
                    v___x_3869_ = l_Lean_instBEqMVarId_beq(v_x_3854_, v_k_x27_3868_);
                    if v___x_3869_ == 0 {
                        if v_isShared_3860_ == 0 {
                            v___x_3871_ = v___x_3859_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3875_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_ks_3856_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_vs_3857_);
                            v___x_3871_ = v_reuseFailAlloc_3875_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3876_ = lean_array_fset(v_ks_3856_, v_x_3853_, v_x_3854_);
                        v___x_3877_ = lean_array_fset(v_vs_3857_, v_x_3853_, v_x_3855_);
                        leanh::lean_dec(v_x_3853_);
                        if v_isShared_3860_ == 0 {
                            leanh::lean_ctor_set(v___x_3859_, 1, v___x_3877_);
                            leanh::lean_ctor_set(v___x_3859_, 0, v___x_3876_);
                            v___x_3879_ = v___x_3859_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3880_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3876_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3877_);
                            v___x_3879_ = v_reuseFailAlloc_3880_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3866_;
            }
            3 => {
                v___x_3872_ = leanh::lean_unsigned_to_nat(1);
                v___x_3873_ = lean_nat_add(v_x_3853_, v___x_3872_);
                leanh::lean_dec(v_x_3853_);
                v_x_3852_ = v___x_3871_;
                v_x_3853_ = v___x_3873_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(
    mut v_n_3882_: *mut leanh::LeanObject,
    mut v_k_3883_: *mut leanh::LeanObject,
    mut v_v_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = leanh::lean_unsigned_to_nat(0);
    v___x_3886_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_n_3882_, v___x_3885_, v_k_3883_, v_v_3884_);
    return v___x_3886_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0()
-> usize {
    let mut v___x_3887_: usize = 0;
    let mut v___x_3888_: usize = 0;
    let mut v___x_3889_: usize = 0;
    v___x_3887_ = 5usize;
    v___x_3888_ = 1usize;
    v___x_3889_ = lean_usize_shift_left(v___x_3888_, v___x_3887_);
    return v___x_3889_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1()
-> usize {
    let mut v___x_3890_: usize = 0;
    let mut v___x_3891_: usize = 0;
    let mut v___x_3892_: usize = 0;
    v___x_3890_ = 1usize;
    v___x_3891_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__0);
    v___x_3892_ = lean_usize_sub(v___x_3891_, v___x_3890_);
    return v___x_3892_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3893_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3893_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(
    mut v_x_3894_: *mut leanh::LeanObject,
    mut v_x_3895_: usize,
    mut v_x_3896_: usize,
    mut v_x_3897_: *mut leanh::LeanObject,
    mut v_x_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: usize = 0;
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v___x_3903_: usize = 0;
    let mut v_j_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v_v_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut v_node_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v___x_3935_: usize = 0;
    let mut v___x_3936_: usize = 0;
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_unused_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: u8 = 0;
    let mut v_ks_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: usize = 0;
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v_reuseFailAlloc_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3894_) == 0 {
                    v_es_3899_ = leanh::lean_ctor_get(v_x_3894_, 0);
                    v___x_3900_ = 5usize;
                    v___x_3901_ = 1usize;
                    v___x_3902_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__1);
                    v___x_3903_ = lean_usize_land(v_x_3895_, v___x_3902_);
                    v_j_3904_ = lean_usize_to_nat(v___x_3903_);
                    v___x_3905_ = lean_array_get_size(v_es_3899_);
                    v___x_3906_ = lean_nat_dec_lt(v_j_3904_, v___x_3905_);
                    if v___x_3906_ == 0 {
                        leanh::lean_dec(v_j_3904_);
                        leanh::lean_dec(v_x_3898_);
                        leanh::lean_dec(v_x_3897_);
                        return v_x_3894_;
                    } else {
                        leanh::lean_inc_ref(v_es_3899_);
                        v_isSharedCheck_3943_ = (!leanh::lean_is_exclusive(v_x_3894_)) as u8;
                        if v_isSharedCheck_3943_ == 0 {
                            v_unused_3944_ = leanh::lean_ctor_get(v_x_3894_, 0);
                            leanh::lean_dec(v_unused_3944_);
                            v___x_3908_ = v_x_3894_;
                            v_isShared_3909_ = v_isSharedCheck_3943_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3894_);
                            v___x_3908_ = leanh::lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3943_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3945_ = leanh::lean_ctor_get(v_x_3894_, 0);
                    v_vs_3946_ = leanh::lean_ctor_get(v_x_3894_, 1);
                    v_isSharedCheck_3966_ = (!leanh::lean_is_exclusive(v_x_3894_)) as u8;
                    if v_isSharedCheck_3966_ == 0 {
                        v___x_3948_ = v_x_3894_;
                        v_isShared_3949_ = v_isSharedCheck_3966_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3946_);
                        leanh::lean_inc(v_ks_3945_);
                        leanh::lean_dec(v_x_3894_);
                        v___x_3948_ = leanh::lean_box(0);
                        v_isShared_3949_ = v_isSharedCheck_3966_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3910_ = lean_array_fget(v_es_3899_, v_j_3904_);
                v___x_3911_ = leanh::lean_box(0);
                v_xs_x27_3912_ = lean_array_fset(v_es_3899_, v_j_3904_, v___x_3911_);
                match leanh::lean_obj_tag(v_v_3910_) {
                    0 => {
                        v_key_3919_ = leanh::lean_ctor_get(v_v_3910_, 0);
                        v_val_3920_ = leanh::lean_ctor_get(v_v_3910_, 1);
                        v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v_v_3910_)) as u8;
                        if v_isSharedCheck_3930_ == 0 {
                            v___x_3922_ = v_v_3910_;
                            v_isShared_3923_ = v_isSharedCheck_3930_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3920_);
                            leanh::lean_inc(v_key_3919_);
                            leanh::lean_dec(v_v_3910_);
                            v___x_3922_ = leanh::lean_box(0);
                            v_isShared_3923_ = v_isSharedCheck_3930_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3931_ = leanh::lean_ctor_get(v_v_3910_, 0);
                        v_isSharedCheck_3941_ = (!leanh::lean_is_exclusive(v_v_3910_)) as u8;
                        if v_isSharedCheck_3941_ == 0 {
                            v___x_3933_ = v_v_3910_;
                            v_isShared_3934_ = v_isSharedCheck_3941_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3931_);
                            leanh::lean_dec(v_v_3910_);
                            v___x_3933_ = leanh::lean_box(0);
                            v_isShared_3934_ = v_isSharedCheck_3941_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3942_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3942_, 0, v_x_3897_);
                        leanh::lean_ctor_set(v___x_3942_, 1, v_x_3898_);
                        v___y_3914_ = v___x_3942_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3915_ = lean_array_fset(v_xs_x27_3912_, v_j_3904_, v___y_3914_);
                leanh::lean_dec(v_j_3904_);
                if v_isShared_3909_ == 0 {
                    leanh::lean_ctor_set(v___x_3908_, 0, v___x_3915_);
                    v___x_3917_ = v___x_3908_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
                    v___x_3917_ = v_reuseFailAlloc_3918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3917_;
            }
            4 => {
                v___x_3924_ = l_Lean_instBEqMVarId_beq(v_x_3897_, v_key_3919_);
                if v___x_3924_ == 0 {
                    leanh::lean_del_object(v___x_3922_);
                    v___x_3925_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3919_,
                        v_val_3920_,
                        v_x_3897_,
                        v_x_3898_,
                    );
                    v___x_3926_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
                    v___y_3914_ = v___x_3926_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3920_);
                    leanh::lean_dec(v_key_3919_);
                    if v_isShared_3923_ == 0 {
                        leanh::lean_ctor_set(v___x_3922_, 1, v_x_3898_);
                        leanh::lean_ctor_set(v___x_3922_, 0, v_x_3897_);
                        v___x_3928_ = v___x_3922_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_x_3897_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_x_3898_);
                        v___x_3928_ = v_reuseFailAlloc_3929_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3914_ = v___x_3928_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3935_ = lean_usize_shift_right(v_x_3895_, v___x_3900_);
                v___x_3936_ = lean_usize_add(v_x_3896_, v___x_3901_);
                v___x_3937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_node_3931_, v___x_3935_, v___x_3936_, v_x_3897_, v_x_3898_);
                if v_isShared_3934_ == 0 {
                    leanh::lean_ctor_set(v___x_3933_, 0, v___x_3937_);
                    v___x_3939_ = v___x_3933_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
                    v___x_3939_ = v_reuseFailAlloc_3940_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3914_ = v___x_3939_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3949_ == 0 {
                    v___x_3951_ = v___x_3948_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3965_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_ks_3945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_vs_3946_);
                    v___x_3951_ = v_reuseFailAlloc_3965_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3952_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v___x_3951_, v_x_3897_, v_x_3898_);
                v___x_3960_ = 7usize;
                v___x_3961_ = lean_usize_dec_le(v___x_3960_, v_x_3896_);
                if v___x_3961_ == 0 {
                    v___x_3962_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3952_);
                    v___x_3963_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3964_ = lean_nat_dec_lt(v___x_3962_, v___x_3963_);
                    leanh::lean_dec(v___x_3962_);
                    v___y_3954_ = v___x_3964_;
                    state = 10;
                    continue;
                } else {
                    v___y_3954_ = v___x_3961_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3954_ == 0 {
                    v_ks_3955_ = leanh::lean_ctor_get(v_newNode_3952_, 0);
                    leanh::lean_inc_ref(v_ks_3955_);
                    v_vs_3956_ = leanh::lean_ctor_get(v_newNode_3952_, 1);
                    leanh::lean_inc_ref(v_vs_3956_);
                    leanh::lean_dec_ref(v_newNode_3952_);
                    v___x_3957_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___closed__2);
                    v___x_3959_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_x_3896_, v_ks_3955_, v_vs_3956_, v___x_3957_, v___x_3958_);
                    leanh::lean_dec_ref(v_vs_3956_);
                    leanh::lean_dec_ref(v_ks_3955_);
                    return v___x_3959_;
                } else {
                    return v_newNode_3952_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(
    mut v_depth_3967_: usize,
    mut v_keys_3968_: *mut leanh::LeanObject,
    mut v_vals_3969_: *mut leanh::LeanObject,
    mut v_i_3970_: *mut leanh::LeanObject,
    mut v_entries_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: u8 = 0;
    let mut v_k_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: u64 = 0;
    let mut v_h_3977_: usize = 0;
    let mut v___x_3978_: usize = 0;
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: usize = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: usize = 0;
    let mut v_h_3983_: usize = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3972_ = lean_array_get_size(v_keys_3968_);
                v___x_3973_ = lean_nat_dec_lt(v_i_3970_, v___x_3972_);
                if v___x_3973_ == 0 {
                    leanh::lean_dec(v_i_3970_);
                    return v_entries_3971_;
                } else {
                    v_k_3974_ = lean_array_fget_borrowed(v_keys_3968_, v_i_3970_);
                    v_v_3975_ = lean_array_fget_borrowed(v_vals_3969_, v_i_3970_);
                    v___x_3976_ = l_Lean_instHashableMVarId_hash(v_k_3974_);
                    v_h_3977_ = lean_uint64_to_usize(v___x_3976_);
                    v___x_3978_ = 5usize;
                    v___x_3979_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3980_ = 1usize;
                    v___x_3981_ = lean_usize_sub(v_depth_3967_, v___x_3980_);
                    v___x_3982_ = lean_usize_mul(v___x_3978_, v___x_3981_);
                    v_h_3983_ = lean_usize_shift_right(v_h_3977_, v___x_3982_);
                    v___x_3984_ = lean_nat_add(v_i_3970_, v___x_3979_);
                    leanh::lean_dec(v_i_3970_);
                    leanh::lean_inc(v_v_3975_);
                    leanh::lean_inc(v_k_3974_);
                    v___x_3985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_entries_3971_, v_h_3983_, v_depth_3967_, v_k_3974_, v_v_3975_);
                    v_i_3970_ = v___x_3984_;
                    v_entries_3971_ = v___x_3985_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg___boxed(
    mut v_depth_3987_: *mut leanh::LeanObject,
    mut v_keys_3988_: *mut leanh::LeanObject,
    mut v_vals_3989_: *mut leanh::LeanObject,
    mut v_i_3990_: *mut leanh::LeanObject,
    mut v_entries_3991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3992_: usize = 0;
    let mut v_res_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3992_ = leanh::lean_unbox_usize(v_depth_3987_);
    leanh::lean_dec(v_depth_3987_);
    v_res_3993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_boxed_3992_, v_keys_3988_, v_vals_3989_, v_i_3990_, v_entries_3991_);
    leanh::lean_dec_ref(v_vals_3989_);
    leanh::lean_dec_ref(v_keys_3988_);
    return v_res_3993_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg___boxed(
    mut v_x_3994_: *mut leanh::LeanObject,
    mut v_x_3995_: *mut leanh::LeanObject,
    mut v_x_3996_: *mut leanh::LeanObject,
    mut v_x_3997_: *mut leanh::LeanObject,
    mut v_x_3998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_20356__boxed_3999_: usize = 0;
    let mut v_x_20357__boxed_4000_: usize = 0;
    let mut v_res_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_20356__boxed_3999_ = leanh::lean_unbox_usize(v_x_3995_);
    leanh::lean_dec(v_x_3995_);
    v_x_20357__boxed_4000_ = leanh::lean_unbox_usize(v_x_3996_);
    leanh::lean_dec(v_x_3996_);
    v_res_4001_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_3994_, v_x_20356__boxed_3999_, v_x_20357__boxed_4000_, v_x_3997_, v_x_3998_);
    return v_res_4001_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(
    mut v_x_4002_: *mut leanh::LeanObject,
    mut v_x_4003_: *mut leanh::LeanObject,
    mut v_x_4004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4005_: u64 = 0;
    let mut v___x_4006_: usize = 0;
    let mut v___x_4007_: usize = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4005_ = l_Lean_instHashableMVarId_hash(v_x_4003_);
    v___x_4006_ = lean_uint64_to_usize(v___x_4005_);
    v___x_4007_ = 1usize;
    v___x_4008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_4002_, v___x_4006_, v___x_4007_, v_x_4003_, v_x_4004_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(
    mut v_mvarId_4009_: *mut leanh::LeanObject,
    mut v_val_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v_depth_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4013_ = lean_st_ref_take(v___y_4011_);
                v_mctx_4014_ = leanh::lean_ctor_get(v___x_4013_, 0);
                v_cache_4015_ = leanh::lean_ctor_get(v___x_4013_, 1);
                v_zetaDeltaFVarIds_4016_ = leanh::lean_ctor_get(v___x_4013_, 2);
                v_postponed_4017_ = leanh::lean_ctor_get(v___x_4013_, 3);
                v_diag_4018_ = leanh::lean_ctor_get(v___x_4013_, 4);
                v_isSharedCheck_4046_ = (!leanh::lean_is_exclusive(v___x_4013_)) as u8;
                if v_isSharedCheck_4046_ == 0 {
                    v___x_4020_ = v___x_4013_;
                    v_isShared_4021_ = v_isSharedCheck_4046_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4018_);
                    leanh::lean_inc(v_postponed_4017_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4016_);
                    leanh::lean_inc(v_cache_4015_);
                    leanh::lean_inc(v_mctx_4014_);
                    leanh::lean_dec(v___x_4013_);
                    v___x_4020_ = leanh::lean_box(0);
                    v_isShared_4021_ = v_isSharedCheck_4046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4022_ = leanh::lean_ctor_get(v_mctx_4014_, 0);
                v_levelAssignDepth_4023_ = leanh::lean_ctor_get(v_mctx_4014_, 1);
                v_lmvarCounter_4024_ = leanh::lean_ctor_get(v_mctx_4014_, 2);
                v_mvarCounter_4025_ = leanh::lean_ctor_get(v_mctx_4014_, 3);
                v_lDecls_4026_ = leanh::lean_ctor_get(v_mctx_4014_, 4);
                v_decls_4027_ = leanh::lean_ctor_get(v_mctx_4014_, 5);
                v_userNames_4028_ = leanh::lean_ctor_get(v_mctx_4014_, 6);
                v_lAssignment_4029_ = leanh::lean_ctor_get(v_mctx_4014_, 7);
                v_eAssignment_4030_ = leanh::lean_ctor_get(v_mctx_4014_, 8);
                v_dAssignment_4031_ = leanh::lean_ctor_get(v_mctx_4014_, 9);
                v_isSharedCheck_4045_ = (!leanh::lean_is_exclusive(v_mctx_4014_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v___x_4033_ = v_mctx_4014_;
                    v_isShared_4034_ = v_isSharedCheck_4045_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_4031_);
                    leanh::lean_inc(v_eAssignment_4030_);
                    leanh::lean_inc(v_lAssignment_4029_);
                    leanh::lean_inc(v_userNames_4028_);
                    leanh::lean_inc(v_decls_4027_);
                    leanh::lean_inc(v_lDecls_4026_);
                    leanh::lean_inc(v_mvarCounter_4025_);
                    leanh::lean_inc(v_lmvarCounter_4024_);
                    leanh::lean_inc(v_levelAssignDepth_4023_);
                    leanh::lean_inc(v_depth_4022_);
                    leanh::lean_dec(v_mctx_4014_);
                    v___x_4033_ = leanh::lean_box(0);
                    v_isShared_4034_ = v_isSharedCheck_4045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4035_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_eAssignment_4030_, v_mvarId_4009_, v_val_4010_);
                if v_isShared_4034_ == 0 {
                    leanh::lean_ctor_set(v___x_4033_, 8, v___x_4035_);
                    v___x_4037_ = v___x_4033_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_depth_4022_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4044_,
                        1,
                        v_levelAssignDepth_4023_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 2, v_lmvarCounter_4024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 3, v_mvarCounter_4025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 4, v_lDecls_4026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 5, v_decls_4027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 6, v_userNames_4028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 7, v_lAssignment_4029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 8, v___x_4035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 9, v_dAssignment_4031_);
                    v___x_4037_ = v_reuseFailAlloc_4044_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4021_ == 0 {
                    leanh::lean_ctor_set(v___x_4020_, 0, v___x_4037_);
                    v___x_4039_ = v___x_4020_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4043_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_cache_4015_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4043_,
                        2,
                        v_zetaDeltaFVarIds_4016_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 3, v_postponed_4017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 4, v_diag_4018_);
                    v___x_4039_ = v_reuseFailAlloc_4043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4040_ = lean_st_ref_set(v___y_4011_, v___x_4039_);
                v___x_4041_ = leanh::lean_box(0);
                v___x_4042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4042_, 0, v___x_4041_);
                return v___x_4042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg___boxed(
    mut v_mvarId_4047_: *mut leanh::LeanObject,
    mut v_val_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(
            v_mvarId_4047_,
            v_val_4048_,
            v___y_4049_,
        );
    leanh::lean_dec(v___y_4049_);
    return v_res_4051_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(
    mut v_as_4052_: *mut leanh::LeanObject,
    mut v_i_4053_: *mut leanh::LeanObject,
    mut v_j_4054_: *mut leanh::LeanObject,
    mut v_bs_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4060_: u8 = 0;
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4076_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4059_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4060_ = lean_nat_dec_eq(v_i_4053_, v_zero_4059_);
                if v_isZero_4060_ == 1 {
                    leanh::lean_dec(v_j_4054_);
                    leanh::lean_dec(v_i_4053_);
                    v___x_4061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4061_, 0, v_bs_4055_);
                    return v___x_4061_;
                } else {
                    v___x_4062_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__6___closed__1;
                    v___x_4063_ =
                        l_Lean_Core_mkFreshUserName(v___x_4062_, v___y_4056_, v___y_4057_);
                    if leanh::lean_obj_tag(v___x_4063_) == 0 {
                        v_a_4064_ = leanh::lean_ctor_get(v___x_4063_, 0);
                        leanh::lean_inc(v_a_4064_);
                        leanh::lean_dec_ref_known(v___x_4063_, 1);
                        v_one_4065_ = leanh::lean_unsigned_to_nat(1);
                        v_n_4066_ = lean_nat_sub(v_i_4053_, v_one_4065_);
                        leanh::lean_dec(v_i_4053_);
                        v___x_4067_ = lean_array_fget_borrowed(v_as_4052_, v_j_4054_);
                        v___x_4068_ = lean_nat_add(v_j_4054_, v_one_4065_);
                        leanh::lean_dec(v_j_4054_);
                        leanh::lean_inc(v___x_4068_);
                        v___x_4069_ = lean_name_append_index_after(v_a_4064_, v___x_4068_);
                        leanh::lean_inc(v___x_4067_);
                        v___x_4070_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4070_, 0, v___x_4069_);
                        leanh::lean_ctor_set(v___x_4070_, 1, v___x_4067_);
                        v___x_4071_ = lean_array_push(v_bs_4055_, v___x_4070_);
                        v_i_4053_ = v_n_4066_;
                        v_j_4054_ = v___x_4068_;
                        v_bs_4055_ = v___x_4071_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4055_);
                        leanh::lean_dec(v_j_4054_);
                        leanh::lean_dec(v_i_4053_);
                        v_a_4073_ = leanh::lean_ctor_get(v___x_4063_, 0);
                        v_isSharedCheck_4080_ =
                            (!leanh::lean_is_exclusive(v___x_4063_)) as u8;
                        if v_isSharedCheck_4080_ == 0 {
                            v___x_4075_ = v___x_4063_;
                            v_isShared_4076_ = v_isSharedCheck_4080_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4073_);
                            leanh::lean_dec(v___x_4063_);
                            v___x_4075_ = leanh::lean_box(0);
                            v_isShared_4076_ = v_isSharedCheck_4080_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4076_ == 0 {
                    v___x_4078_ = v___x_4075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4079_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
                    v___x_4078_ = v_reuseFailAlloc_4079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg___boxed(
    mut v_as_4081_: *mut leanh::LeanObject,
    mut v_i_4082_: *mut leanh::LeanObject,
    mut v_j_4083_: *mut leanh::LeanObject,
    mut v_bs_4084_: *mut leanh::LeanObject,
    mut v___y_4085_: *mut leanh::LeanObject,
    mut v___y_4086_: *mut leanh::LeanObject,
    mut v___y_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_4081_, v_i_4082_, v_j_4083_, v_bs_4084_, v___y_4085_, v___y_4086_);
    leanh::lean_dec(v___y_4086_);
    leanh::lean_dec_ref(v___y_4085_);
    leanh::lean_dec_ref(v_as_4081_);
    return v_res_4088_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(
    mut v_msgData_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
    mut v___y_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = lean_st_ref_get(v___y_4093_);
    v_env_4096_ = leanh::lean_ctor_get(v___x_4095_, 0);
    leanh::lean_inc_ref(v_env_4096_);
    leanh::lean_dec(v___x_4095_);
    v___x_4097_ = lean_st_ref_get(v___y_4091_);
    v_mctx_4098_ = leanh::lean_ctor_get(v___x_4097_, 0);
    leanh::lean_inc_ref(v_mctx_4098_);
    leanh::lean_dec(v___x_4097_);
    v_lctx_4099_ = leanh::lean_ctor_get(v___y_4090_, 2);
    v_options_4100_ = leanh::lean_ctor_get(v___y_4092_, 2);
    leanh::lean_inc_ref(v_options_4100_);
    leanh::lean_inc_ref(v_lctx_4099_);
    v___x_4101_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4101_, 0, v_env_4096_);
    leanh::lean_ctor_set(v___x_4101_, 1, v_mctx_4098_);
    leanh::lean_ctor_set(v___x_4101_, 2, v_lctx_4099_);
    leanh::lean_ctor_set(v___x_4101_, 3, v_options_4100_);
    v___x_4102_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4102_, 0, v___x_4101_);
    leanh::lean_ctor_set(v___x_4102_, 1, v_msgData_4089_);
    v___x_4103_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4103_, 0, v___x_4102_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14___boxed(
    mut v_msgData_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msgData_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
    leanh::lean_dec(v___y_4108_);
    leanh::lean_dec_ref(v___y_4107_);
    leanh::lean_dec(v___y_4106_);
    leanh::lean_dec_ref(v___y_4105_);
    return v_res_4110_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(
    mut v_msg_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4117_ = leanh::lean_ctor_get(v___y_4114_, 5);
                v___x_4118_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
                v_a_4119_ = leanh::lean_ctor_get(v___x_4118_, 0);
                v_isSharedCheck_4127_ = (!leanh::lean_is_exclusive(v___x_4118_)) as u8;
                if v_isSharedCheck_4127_ == 0 {
                    v___x_4121_ = v___x_4118_;
                    v_isShared_4122_ = v_isSharedCheck_4127_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4119_);
                    leanh::lean_dec(v___x_4118_);
                    v___x_4121_ = leanh::lean_box(0);
                    v_isShared_4122_ = v_isSharedCheck_4127_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4117_);
                v___x_4123_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4123_, 0, v_ref_4117_);
                leanh::lean_ctor_set(v___x_4123_, 1, v_a_4119_);
                if v_isShared_4122_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4121_, 1);
                    leanh::lean_ctor_set(v___x_4121_, 0, v___x_4123_);
                    v___x_4125_ = v___x_4121_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
                    v___x_4125_ = v_reuseFailAlloc_4126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg___boxed(
    mut v_msg_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    leanh::lean_dec(v___y_4132_);
    leanh::lean_dec_ref(v___y_4131_);
    leanh::lean_dec(v___y_4130_);
    leanh::lean_dec_ref(v___y_4129_);
    return v_res_4134_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(
    mut v_u_4135_: *mut leanh::LeanObject,
    mut v_as_4136_: *mut leanh::LeanObject,
    mut v_i_4137_: usize,
    mut v_stop_4138_: usize,
    mut v_b_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: usize = 0;
    let mut v___x_4142_: usize = 0;
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4140_ = lean_usize_dec_eq(v_i_4137_, v_stop_4138_);
                if v___x_4140_ == 0 {
                    v___x_4141_ = 1usize;
                    v___x_4142_ = lean_usize_sub(v_i_4137_, v___x_4141_);
                    v___x_4143_ = lean_array_uget_borrowed(v_as_4136_, v___x_4142_);
                    leanh::lean_inc(v___x_4143_);
                    leanh::lean_inc(v_u_4135_);
                    v___x_4144_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(
                        v_u_4135_,
                        v___x_4143_,
                        v_b_4139_,
                    );
                    v_i_4137_ = v___x_4142_;
                    v_b_4139_ = v___x_4144_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_u_4135_);
                    return v_b_4139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7___boxed(
    mut v_u_4146_: *mut leanh::LeanObject,
    mut v_as_4147_: *mut leanh::LeanObject,
    mut v_i_4148_: *mut leanh::LeanObject,
    mut v_stop_4149_: *mut leanh::LeanObject,
    mut v_b_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4151_: usize = 0;
    let mut v_stop_boxed_4152_: usize = 0;
    let mut v_res_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4151_ = leanh::lean_unbox_usize(v_i_4148_);
    leanh::lean_dec(v_i_4148_);
    v_stop_boxed_4152_ = leanh::lean_unbox_usize(v_stop_4149_);
    leanh::lean_dec(v_stop_4149_);
    v_res_4153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_4146_, v_as_4147_, v_i_boxed_4151_, v_stop_boxed_4152_, v_b_4150_);
    leanh::lean_dec_ref(v_as_4147_);
    return v_res_4153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(
    mut v_sz_4154_: usize,
    mut v_i_4155_: usize,
    mut v_bs_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
    mut v___y_4159_: *mut leanh::LeanObject,
    mut v___y_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4162_: u8 = 0;
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: usize = 0;
    let mut v___x_4170_: usize = 0;
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4162_ = lean_usize_dec_lt(v_i_4155_, v_sz_4154_);
                if v___x_4162_ == 0 {
                    v___x_4163_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4163_, 0, v_bs_4156_);
                    return v___x_4163_;
                } else {
                    v_v_4164_ = lean_array_uget_borrowed(v_bs_4156_, v_i_4155_);
                    leanh::lean_inc(v_v_4164_);
                    v___x_4165_ = l_Lean_Meta_mkEqRefl(
                        v_v_4164_,
                        v___y_4157_,
                        v___y_4158_,
                        v___y_4159_,
                        v___y_4160_,
                    );
                    if leanh::lean_obj_tag(v___x_4165_) == 0 {
                        v_a_4166_ = leanh::lean_ctor_get(v___x_4165_, 0);
                        leanh::lean_inc(v_a_4166_);
                        leanh::lean_dec_ref_known(v___x_4165_, 1);
                        v___x_4167_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4168_ = lean_array_uset(v_bs_4156_, v_i_4155_, v___x_4167_);
                        v___x_4169_ = 1usize;
                        v___x_4170_ = lean_usize_add(v_i_4155_, v___x_4169_);
                        v___x_4171_ = lean_array_uset(v_bs_x27_4168_, v_i_4155_, v_a_4166_);
                        v_i_4155_ = v___x_4170_;
                        v_bs_4156_ = v___x_4171_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4156_);
                        v_a_4173_ = leanh::lean_ctor_get(v___x_4165_, 0);
                        v_isSharedCheck_4180_ =
                            (!leanh::lean_is_exclusive(v___x_4165_)) as u8;
                        if v_isSharedCheck_4180_ == 0 {
                            v___x_4175_ = v___x_4165_;
                            v_isShared_4176_ = v_isSharedCheck_4180_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4173_);
                            leanh::lean_dec(v___x_4165_);
                            v___x_4175_ = leanh::lean_box(0);
                            v_isShared_4176_ = v_isSharedCheck_4180_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6___boxed(
    mut v_sz_4181_: *mut leanh::LeanObject,
    mut v_i_4182_: *mut leanh::LeanObject,
    mut v_bs_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4189_: usize = 0;
    let mut v_i_boxed_4190_: usize = 0;
    let mut v_res_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4189_ = leanh::lean_unbox_usize(v_sz_4181_);
    leanh::lean_dec(v_sz_4181_);
    v_i_boxed_4190_ = leanh::lean_unbox_usize(v_i_4182_);
    leanh::lean_dec(v_i_4182_);
    v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_boxed_4189_, v_i_boxed_4190_, v_bs_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
    leanh::lean_dec(v___y_4187_);
    leanh::lean_dec_ref(v___y_4186_);
    leanh::lean_dec(v___y_4185_);
    leanh::lean_dec_ref(v___y_4184_);
    return v_res_4191_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(
    mut v_a_4192_: *mut leanh::LeanObject,
    mut v_b_4193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: u8 = 0;
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4194_ = leanh::lean_ctor_get(v_a_4192_, 0);
                v_start_4195_ = leanh::lean_ctor_get(v_a_4192_, 1);
                v_stop_4196_ = leanh::lean_ctor_get(v_a_4192_, 2);
                v_isSharedCheck_4209_ = (!leanh::lean_is_exclusive(v_a_4192_)) as u8;
                if v_isSharedCheck_4209_ == 0 {
                    v___x_4198_ = v_a_4192_;
                    v_isShared_4199_ = v_isSharedCheck_4209_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_4196_);
                    leanh::lean_inc(v_start_4195_);
                    leanh::lean_inc(v_array_4194_);
                    leanh::lean_dec(v_a_4192_);
                    v___x_4198_ = leanh::lean_box(0);
                    v_isShared_4199_ = v_isSharedCheck_4209_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4200_ = lean_nat_dec_lt(v_start_4195_, v_stop_4196_);
                if v___x_4200_ == 0 {
                    leanh::lean_del_object(v___x_4198_);
                    leanh::lean_dec(v_stop_4196_);
                    leanh::lean_dec(v_start_4195_);
                    leanh::lean_dec_ref(v_array_4194_);
                    return v_b_4193_;
                } else {
                    v___x_4201_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4202_ = lean_nat_add(v_start_4195_, v___x_4201_);
                    leanh::lean_inc_ref(v_array_4194_);
                    if v_isShared_4199_ == 0 {
                        leanh::lean_ctor_set(v___x_4198_, 1, v___x_4202_);
                        v___x_4204_ = v___x_4198_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4208_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_array_4194_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4202_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 2, v_stop_4196_);
                        v___x_4204_ = v_reuseFailAlloc_4208_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4205_ = lean_array_fget(v_array_4194_, v_start_4195_);
                leanh::lean_dec(v_start_4195_);
                leanh::lean_dec_ref(v_array_4194_);
                v___x_4206_ = lean_array_push(v_b_4193_, v___x_4205_);
                v_a_4192_ = v___x_4204_;
                v_b_4193_ = v___x_4206_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(
    mut v___x_4210_: *mut leanh::LeanObject,
    mut v_a_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
    mut v___y_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20043__overap_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4221_ = l_Lean_instInhabitedExpr;
    v___x_20043__overap_4222_ = l_instInhabitedOfMonad___redArg(v___x_4210_, v___x_4221_);
    leanh::lean_inc(v___y_4219_);
    leanh::lean_inc_ref(v___y_4218_);
    leanh::lean_inc(v___y_4217_);
    leanh::lean_inc_ref(v___y_4216_);
    leanh::lean_inc(v___y_4215_);
    leanh::lean_inc_ref(v___y_4214_);
    leanh::lean_inc(v___y_4213_);
    leanh::lean_inc_ref(v___y_4212_);
    v___x_4223_ = leanh::lean_apply_9(
        v___x_20043__overap_4222_,
        v___y_4212_,
        v___y_4213_,
        v___y_4214_,
        v___y_4215_,
        v___y_4216_,
        v___y_4217_,
        v___y_4218_,
        v___y_4219_,
        leanh::lean_box(0),
    );
    return v___x_4223_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed(
    mut v___x_4224_: *mut leanh::LeanObject,
    mut v_a_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0(v___x_4224_, v_a_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
    leanh::lean_dec(v___y_4233_);
    leanh::lean_dec_ref(v___y_4232_);
    leanh::lean_dec(v___y_4231_);
    leanh::lean_dec_ref(v___y_4230_);
    leanh::lean_dec(v___y_4229_);
    leanh::lean_dec_ref(v___y_4228_);
    leanh::lean_dec(v___y_4227_);
    leanh::lean_dec_ref(v___y_4226_);
    leanh::lean_dec_ref(v_a_4225_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(
    mut v_k_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v_b_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4245_);
    leanh::lean_inc_ref(v___y_4244_);
    leanh::lean_inc(v___y_4243_);
    leanh::lean_inc_ref(v___y_4242_);
    leanh::lean_inc(v___y_4240_);
    leanh::lean_inc_ref(v___y_4239_);
    leanh::lean_inc(v___y_4238_);
    leanh::lean_inc_ref(v___y_4237_);
    v___x_4247_ = leanh::lean_apply_10(
        v_k_4236_,
        v_b_4241_,
        v___y_4237_,
        v___y_4238_,
        v___y_4239_,
        v___y_4240_,
        v___y_4242_,
        v___y_4243_,
        v___y_4244_,
        v___y_4245_,
        leanh::lean_box(0),
    );
    return v___x_4247_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed(
    mut v_k_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
    mut v___y_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v_b_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0(v_k_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v_b_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
    leanh::lean_dec(v___y_4257_);
    leanh::lean_dec_ref(v___y_4256_);
    leanh::lean_dec(v___y_4255_);
    leanh::lean_dec_ref(v___y_4254_);
    leanh::lean_dec(v___y_4252_);
    leanh::lean_dec_ref(v___y_4251_);
    leanh::lean_dec(v___y_4250_);
    leanh::lean_dec_ref(v___y_4249_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(
    mut v_name_4260_: *mut leanh::LeanObject,
    mut v_bi_4261_: u8,
    mut v_type_4262_: *mut leanh::LeanObject,
    mut v_k_4263_: *mut leanh::LeanObject,
    mut v_kind_4264_: u8,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
    mut v___y_4268_: *mut leanh::LeanObject,
    mut v___y_4269_: *mut leanh::LeanObject,
    mut v___y_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
    mut v___y_4272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4268_);
                leanh::lean_inc_ref(v___y_4267_);
                leanh::lean_inc(v___y_4266_);
                leanh::lean_inc_ref(v___y_4265_);
                v___f_4274_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                leanh::lean_closure_set(v___f_4274_, 0, v_k_4263_);
                leanh::lean_closure_set(v___f_4274_, 1, v___y_4265_);
                leanh::lean_closure_set(v___f_4274_, 2, v___y_4266_);
                leanh::lean_closure_set(v___f_4274_, 3, v___y_4267_);
                leanh::lean_closure_set(v___f_4274_, 4, v___y_4268_);
                v___x_4275_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_4260_,
                    v_bi_4261_,
                    v_type_4262_,
                    v___f_4274_,
                    v_kind_4264_,
                    v___y_4269_,
                    v___y_4270_,
                    v___y_4271_,
                    v___y_4272_,
                );
                if leanh::lean_obj_tag(v___x_4275_) == 0 {
                    return v___x_4275_;
                } else {
                    v_a_4276_ = leanh::lean_ctor_get(v___x_4275_, 0);
                    v_isSharedCheck_4283_ = (!leanh::lean_is_exclusive(v___x_4275_)) as u8;
                    if v_isSharedCheck_4283_ == 0 {
                        v___x_4278_ = v___x_4275_;
                        v_isShared_4279_ = v_isSharedCheck_4283_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4276_);
                        leanh::lean_dec(v___x_4275_);
                        v___x_4278_ = leanh::lean_box(0);
                        v_isShared_4279_ = v_isSharedCheck_4283_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4279_ == 0 {
                    v___x_4281_ = v___x_4278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg___boxed(
    mut v_name_4284_: *mut leanh::LeanObject,
    mut v_bi_4285_: *mut leanh::LeanObject,
    mut v_type_4286_: *mut leanh::LeanObject,
    mut v_k_4287_: *mut leanh::LeanObject,
    mut v_kind_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
    mut v___y_4294_: *mut leanh::LeanObject,
    mut v___y_4295_: *mut leanh::LeanObject,
    mut v___y_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4298_: u8 = 0;
    let mut v_kind_boxed_4299_: u8 = 0;
    let mut v_res_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4298_ = (leanh::lean_unbox(v_bi_4285_) as u8);
    v_kind_boxed_4299_ = (leanh::lean_unbox(v_kind_4288_) as u8);
    v_res_4300_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_4284_, v_bi_boxed_4298_, v_type_4286_, v_k_4287_, v_kind_boxed_4299_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
    leanh::lean_dec(v___y_4296_);
    leanh::lean_dec_ref(v___y_4295_);
    leanh::lean_dec(v___y_4294_);
    leanh::lean_dec_ref(v___y_4293_);
    leanh::lean_dec(v___y_4292_);
    leanh::lean_dec_ref(v___y_4291_);
    leanh::lean_dec(v___y_4290_);
    leanh::lean_dec_ref(v___y_4289_);
    return v_res_4300_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed(
    mut v_acc_4305_: *mut leanh::LeanObject,
    mut v_declInfos_4306_: *mut leanh::LeanObject,
    mut v_k_4307_: *mut leanh::LeanObject,
    mut v_kind_4308_: *mut leanh::LeanObject,
    mut v_x_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
    mut v___y_4311_: *mut leanh::LeanObject,
    mut v___y_4312_: *mut leanh::LeanObject,
    mut v___y_4313_: *mut leanh::LeanObject,
    mut v___y_4314_: *mut leanh::LeanObject,
    mut v___y_4315_: *mut leanh::LeanObject,
    mut v___y_4316_: *mut leanh::LeanObject,
    mut v___y_4317_: *mut leanh::LeanObject,
    mut v___y_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_4319_: u8 = 0;
    let mut v_res_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4319_ = (leanh::lean_unbox(v_kind_4308_) as u8);
    v_res_4320_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(v_acc_4305_, v_declInfos_4306_, v_k_4307_, v_kind_boxed_4319_, v_x_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
    leanh::lean_dec(v___y_4317_);
    leanh::lean_dec_ref(v___y_4316_);
    leanh::lean_dec(v___y_4315_);
    leanh::lean_dec_ref(v___y_4314_);
    leanh::lean_dec(v___y_4313_);
    leanh::lean_dec_ref(v___y_4312_);
    leanh::lean_dec(v___y_4311_);
    leanh::lean_dec_ref(v___y_4310_);
    return v_res_4320_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(
    mut v_declInfos_4321_: *mut leanh::LeanObject,
    mut v_k_4322_: *mut leanh::LeanObject,
    mut v_kind_4323_: u8,
    mut v_acc_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
    mut v___y_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
    mut v___y_4329_: *mut leanh::LeanObject,
    mut v___y_4330_: *mut leanh::LeanObject,
    mut v___y_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v_toFunctor_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4361_: u8 = 0;
    let mut v___f_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v_toFunctor_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v___f_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v_toFunctor_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___f_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: u8 = 0;
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: u8 = 0;
    let mut v___f_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: u8 = 0;
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4447_: u8 = 0;
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4451_: u8 = 0;
    let mut v_reuseFailAlloc_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v_unused_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4456_: u8 = 0;
    let mut v_unused_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut v_unused_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4462_: u8 = 0;
    let mut v_unused_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_unused_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut v_unused_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4334_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__1,
                );
                v_toApplicative_4335_ = leanh::lean_ctor_get(v___x_4334_, 0);
                v_toFunctor_4336_ = leanh::lean_ctor_get(v_toApplicative_4335_, 0);
                v_toSeq_4337_ = leanh::lean_ctor_get(v_toApplicative_4335_, 2);
                v_toSeqLeft_4338_ = leanh::lean_ctor_get(v_toApplicative_4335_, 3);
                v_toSeqRight_4339_ = leanh::lean_ctor_get(v_toApplicative_4335_, 4);
                v___f_4340_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__2;
                v___f_4341_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_4336_, 2);
                v___f_4342_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4342_, 0, v_toFunctor_4336_);
                v___f_4343_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4343_, 0, v_toFunctor_4336_);
                v___x_4344_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4344_, 0, v___f_4342_);
                leanh::lean_ctor_set(v___x_4344_, 1, v___f_4343_);
                leanh::lean_inc(v_toSeqRight_4339_);
                v___f_4345_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4345_, 0, v_toSeqRight_4339_);
                leanh::lean_inc(v_toSeqLeft_4338_);
                v___f_4346_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4346_, 0, v_toSeqLeft_4338_);
                leanh::lean_inc(v_toSeq_4337_);
                v___f_4347_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4347_, 0, v_toSeq_4337_);
                v___x_4348_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4348_, 0, v___x_4344_);
                leanh::lean_ctor_set(v___x_4348_, 1, v___f_4340_);
                leanh::lean_ctor_set(v___x_4348_, 2, v___f_4347_);
                leanh::lean_ctor_set(v___x_4348_, 3, v___f_4346_);
                leanh::lean_ctor_set(v___x_4348_, 4, v___f_4345_);
                v___x_4349_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4349_, 0, v___x_4348_);
                leanh::lean_ctor_set(v___x_4349_, 1, v___f_4341_);
                v___x_4350_ = l_StateRefT_x27_instMonad___redArg(v___x_4349_);
                v_toApplicative_4351_ = leanh::lean_ctor_get(v___x_4350_, 0);
                v_isSharedCheck_4468_ = (!leanh::lean_is_exclusive(v___x_4350_)) as u8;
                if v_isSharedCheck_4468_ == 0 {
                    v_unused_4469_ = leanh::lean_ctor_get(v___x_4350_, 1);
                    leanh::lean_dec(v_unused_4469_);
                    v___x_4353_ = v___x_4350_;
                    v_isShared_4354_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4351_);
                    leanh::lean_dec(v___x_4350_);
                    v___x_4353_ = leanh::lean_box(0);
                    v_isShared_4354_ = v_isSharedCheck_4468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4355_ = leanh::lean_ctor_get(v_toApplicative_4351_, 0);
                v_toSeq_4356_ = leanh::lean_ctor_get(v_toApplicative_4351_, 2);
                v_toSeqLeft_4357_ = leanh::lean_ctor_get(v_toApplicative_4351_, 3);
                v_toSeqRight_4358_ = leanh::lean_ctor_get(v_toApplicative_4351_, 4);
                v_isSharedCheck_4466_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4351_)) as u8;
                if v_isSharedCheck_4466_ == 0 {
                    v_unused_4467_ = leanh::lean_ctor_get(v_toApplicative_4351_, 1);
                    leanh::lean_dec(v_unused_4467_);
                    v___x_4360_ = v_toApplicative_4351_;
                    v_isShared_4361_ = v_isSharedCheck_4466_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4358_);
                    leanh::lean_inc(v_toSeqLeft_4357_);
                    leanh::lean_inc(v_toSeq_4356_);
                    leanh::lean_inc(v_toFunctor_4355_);
                    leanh::lean_dec(v_toApplicative_4351_);
                    v___x_4360_ = leanh::lean_box(0);
                    v_isShared_4361_ = v_isSharedCheck_4466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4362_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__4;
                v___f_4363_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_4355_);
                v___f_4364_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4364_, 0, v_toFunctor_4355_);
                v___f_4365_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4365_, 0, v_toFunctor_4355_);
                v___x_4366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4366_, 0, v___f_4364_);
                leanh::lean_ctor_set(v___x_4366_, 1, v___f_4365_);
                v___f_4367_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4367_, 0, v_toSeqRight_4358_);
                v___f_4368_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4368_, 0, v_toSeqLeft_4357_);
                v___f_4369_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4369_, 0, v_toSeq_4356_);
                if v_isShared_4361_ == 0 {
                    leanh::lean_ctor_set(v___x_4360_, 4, v___f_4367_);
                    leanh::lean_ctor_set(v___x_4360_, 3, v___f_4368_);
                    leanh::lean_ctor_set(v___x_4360_, 2, v___f_4369_);
                    leanh::lean_ctor_set(v___x_4360_, 1, v___f_4362_);
                    leanh::lean_ctor_set(v___x_4360_, 0, v___x_4366_);
                    v___x_4371_ = v___x_4360_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4366_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 1, v___f_4362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 2, v___f_4369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 3, v___f_4368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 4, v___f_4367_);
                    v___x_4371_ = v_reuseFailAlloc_4465_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4354_ == 0 {
                    leanh::lean_ctor_set(v___x_4353_, 1, v___f_4363_);
                    leanh::lean_ctor_set(v___x_4353_, 0, v___x_4371_);
                    v___x_4373_ = v___x_4353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4464_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___f_4363_);
                    v___x_4373_ = v_reuseFailAlloc_4464_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4374_ = l_StateRefT_x27_instMonad___redArg(v___x_4373_);
                v_toApplicative_4375_ = leanh::lean_ctor_get(v___x_4374_, 0);
                v_isSharedCheck_4462_ = (!leanh::lean_is_exclusive(v___x_4374_)) as u8;
                if v_isSharedCheck_4462_ == 0 {
                    v_unused_4463_ = leanh::lean_ctor_get(v___x_4374_, 1);
                    leanh::lean_dec(v_unused_4463_);
                    v___x_4377_ = v___x_4374_;
                    v_isShared_4378_ = v_isSharedCheck_4462_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4375_);
                    leanh::lean_dec(v___x_4374_);
                    v___x_4377_ = leanh::lean_box(0);
                    v_isShared_4378_ = v_isSharedCheck_4462_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4379_ = leanh::lean_ctor_get(v_toApplicative_4375_, 0);
                v_toSeq_4380_ = leanh::lean_ctor_get(v_toApplicative_4375_, 2);
                v_toSeqLeft_4381_ = leanh::lean_ctor_get(v_toApplicative_4375_, 3);
                v_toSeqRight_4382_ = leanh::lean_ctor_get(v_toApplicative_4375_, 4);
                v_isSharedCheck_4460_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4375_)) as u8;
                if v_isSharedCheck_4460_ == 0 {
                    v_unused_4461_ = leanh::lean_ctor_get(v_toApplicative_4375_, 1);
                    leanh::lean_dec(v_unused_4461_);
                    v___x_4384_ = v_toApplicative_4375_;
                    v_isShared_4385_ = v_isSharedCheck_4460_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4382_);
                    leanh::lean_inc(v_toSeqLeft_4381_);
                    leanh::lean_inc(v_toSeq_4380_);
                    leanh::lean_inc(v_toFunctor_4379_);
                    leanh::lean_dec(v_toApplicative_4375_);
                    v___x_4384_ = leanh::lean_box(0);
                    v_isShared_4385_ = v_isSharedCheck_4460_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4386_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__0;
                v___f_4387_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__1;
                leanh::lean_inc_ref(v_toFunctor_4379_);
                v___f_4388_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4388_, 0, v_toFunctor_4379_);
                v___f_4389_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4389_, 0, v_toFunctor_4379_);
                v___x_4390_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4390_, 0, v___f_4388_);
                leanh::lean_ctor_set(v___x_4390_, 1, v___f_4389_);
                v___f_4391_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4391_, 0, v_toSeqRight_4382_);
                v___f_4392_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4392_, 0, v_toSeqLeft_4381_);
                v___f_4393_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4393_, 0, v_toSeq_4380_);
                if v_isShared_4385_ == 0 {
                    leanh::lean_ctor_set(v___x_4384_, 4, v___f_4391_);
                    leanh::lean_ctor_set(v___x_4384_, 3, v___f_4392_);
                    leanh::lean_ctor_set(v___x_4384_, 2, v___f_4393_);
                    leanh::lean_ctor_set(v___x_4384_, 1, v___f_4386_);
                    leanh::lean_ctor_set(v___x_4384_, 0, v___x_4390_);
                    v___x_4395_ = v___x_4384_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4390_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 1, v___f_4386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 2, v___f_4393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 3, v___f_4392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 4, v___f_4391_);
                    v___x_4395_ = v_reuseFailAlloc_4459_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4378_ == 0 {
                    leanh::lean_ctor_set(v___x_4377_, 1, v___f_4387_);
                    leanh::lean_ctor_set(v___x_4377_, 0, v___x_4395_);
                    v___x_4397_ = v___x_4377_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 1, v___f_4387_);
                    v___x_4397_ = v_reuseFailAlloc_4458_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4398_ = l_StateRefT_x27_instMonad___redArg(v___x_4397_);
                v_toApplicative_4399_ = leanh::lean_ctor_get(v___x_4398_, 0);
                v_isSharedCheck_4456_ = (!leanh::lean_is_exclusive(v___x_4398_)) as u8;
                if v_isSharedCheck_4456_ == 0 {
                    v_unused_4457_ = leanh::lean_ctor_get(v___x_4398_, 1);
                    leanh::lean_dec(v_unused_4457_);
                    v___x_4401_ = v___x_4398_;
                    v_isShared_4402_ = v_isSharedCheck_4456_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_4399_);
                    leanh::lean_dec(v___x_4398_);
                    v___x_4401_ = leanh::lean_box(0);
                    v_isShared_4402_ = v_isSharedCheck_4456_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_toFunctor_4403_ = leanh::lean_ctor_get(v_toApplicative_4399_, 0);
                v_toSeq_4404_ = leanh::lean_ctor_get(v_toApplicative_4399_, 2);
                v_toSeqLeft_4405_ = leanh::lean_ctor_get(v_toApplicative_4399_, 3);
                v_toSeqRight_4406_ = leanh::lean_ctor_get(v_toApplicative_4399_, 4);
                v_isSharedCheck_4454_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_4399_)) as u8;
                if v_isSharedCheck_4454_ == 0 {
                    v_unused_4455_ = leanh::lean_ctor_get(v_toApplicative_4399_, 1);
                    leanh::lean_dec(v_unused_4455_);
                    v___x_4408_ = v_toApplicative_4399_;
                    v_isShared_4409_ = v_isSharedCheck_4454_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_4406_);
                    leanh::lean_inc(v_toSeqLeft_4405_);
                    leanh::lean_inc(v_toSeq_4404_);
                    leanh::lean_inc(v_toFunctor_4403_);
                    leanh::lean_dec(v_toApplicative_4399_);
                    v___x_4408_ = leanh::lean_box(0);
                    v_isShared_4409_ = v_isSharedCheck_4454_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___f_4410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__2;
                v___f_4411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___closed__3;
                leanh::lean_inc_ref(v_toFunctor_4403_);
                v___f_4412_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4412_, 0, v_toFunctor_4403_);
                v___f_4413_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4413_, 0, v_toFunctor_4403_);
                v___x_4414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4414_, 0, v___f_4412_);
                leanh::lean_ctor_set(v___x_4414_, 1, v___f_4413_);
                v___f_4415_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4415_, 0, v_toSeqRight_4406_);
                v___f_4416_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4416_, 0, v_toSeqLeft_4405_);
                v___f_4417_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_4417_, 0, v_toSeq_4404_);
                if v_isShared_4409_ == 0 {
                    leanh::lean_ctor_set(v___x_4408_, 4, v___f_4415_);
                    leanh::lean_ctor_set(v___x_4408_, 3, v___f_4416_);
                    leanh::lean_ctor_set(v___x_4408_, 2, v___f_4417_);
                    leanh::lean_ctor_set(v___x_4408_, 1, v___f_4410_);
                    leanh::lean_ctor_set(v___x_4408_, 0, v___x_4414_);
                    v___x_4419_ = v___x_4408_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4453_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 1, v___f_4410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 2, v___f_4417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 3, v___f_4416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 4, v___f_4415_);
                    v___x_4419_ = v_reuseFailAlloc_4453_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4402_ == 0 {
                    leanh::lean_ctor_set(v___x_4401_, 1, v___f_4411_);
                    leanh::lean_ctor_set(v___x_4401_, 0, v___x_4419_);
                    v___x_4421_ = v___x_4401_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 1, v___f_4411_);
                    v___x_4421_ = v_reuseFailAlloc_4452_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4422_ = lean_array_get_size(v_acc_4324_);
                v___x_4423_ = lean_array_get_size(v_declInfos_4321_);
                v___x_4424_ = lean_nat_dec_lt(v___x_4422_, v___x_4423_);
                if v___x_4424_ == 0 {
                    leanh::lean_dec_ref(v___x_4421_);
                    leanh::lean_dec_ref(v_declInfos_4321_);
                    leanh::lean_inc(v___y_4332_);
                    leanh::lean_inc_ref(v___y_4331_);
                    leanh::lean_inc(v___y_4330_);
                    leanh::lean_inc_ref(v___y_4329_);
                    leanh::lean_inc(v___y_4328_);
                    leanh::lean_inc_ref(v___y_4327_);
                    leanh::lean_inc(v___y_4326_);
                    leanh::lean_inc_ref(v___y_4325_);
                    v___x_4425_ = leanh::lean_apply_10(
                        v_k_4322_,
                        v_acc_4324_,
                        v___y_4325_,
                        v___y_4326_,
                        v___y_4327_,
                        v___y_4328_,
                        v___y_4329_,
                        v___y_4330_,
                        v___y_4331_,
                        v___y_4332_,
                        leanh::lean_box(0),
                    );
                    return v___x_4425_;
                } else {
                    v___f_4426_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                    leanh::lean_closure_set(v___f_4426_, 0, v___x_4421_);
                    v___x_4427_ = leanh::lean_box(0);
                    v___x_4428_ = 0;
                    v___f_4429_ = leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_4429_, 0, v___f_4426_);
                    v___x_4430_ = leanh::lean_box((v___x_4428_) as usize);
                    v___x_4431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4431_, 0, v___x_4430_);
                    leanh::lean_ctor_set(v___x_4431_, 1, v___f_4429_);
                    v___x_4432_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4432_, 0, v___x_4427_);
                    leanh::lean_ctor_set(v___x_4432_, 1, v___x_4431_);
                    v___x_4433_ = lean_array_get(v___x_4432_, v_declInfos_4321_, v___x_4422_);
                    leanh::lean_dec_ref_known(v___x_4432_, 2);
                    v_snd_4434_ = leanh::lean_ctor_get(v___x_4433_, 1);
                    leanh::lean_inc(v_snd_4434_);
                    v_fst_4435_ = leanh::lean_ctor_get(v___x_4433_, 0);
                    leanh::lean_inc(v_fst_4435_);
                    leanh::lean_dec(v___x_4433_);
                    v_fst_4436_ = leanh::lean_ctor_get(v_snd_4434_, 0);
                    leanh::lean_inc(v_fst_4436_);
                    v_snd_4437_ = leanh::lean_ctor_get(v_snd_4434_, 1);
                    leanh::lean_inc(v_snd_4437_);
                    leanh::lean_dec(v_snd_4434_);
                    leanh::lean_inc(v___y_4332_);
                    leanh::lean_inc_ref(v___y_4331_);
                    leanh::lean_inc(v___y_4330_);
                    leanh::lean_inc_ref(v___y_4329_);
                    leanh::lean_inc(v___y_4328_);
                    leanh::lean_inc_ref(v___y_4327_);
                    leanh::lean_inc(v___y_4326_);
                    leanh::lean_inc_ref(v___y_4325_);
                    leanh::lean_inc_ref(v_acc_4324_);
                    v___x_4438_ = leanh::lean_apply_10(
                        v_snd_4437_,
                        v_acc_4324_,
                        v___y_4325_,
                        v___y_4326_,
                        v___y_4327_,
                        v___y_4328_,
                        v___y_4329_,
                        v___y_4330_,
                        v___y_4331_,
                        v___y_4332_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_4438_) == 0 {
                        v_a_4439_ = leanh::lean_ctor_get(v___x_4438_, 0);
                        leanh::lean_inc(v_a_4439_);
                        leanh::lean_dec_ref_known(v___x_4438_, 1);
                        v___x_4440_ = leanh::lean_box((v_kind_4323_) as usize);
                        v___f_4441_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1___boxed as *mut core::ffi::c_void, 14, 4);
                        leanh::lean_closure_set(v___f_4441_, 0, v_acc_4324_);
                        leanh::lean_closure_set(v___f_4441_, 1, v_declInfos_4321_);
                        leanh::lean_closure_set(v___f_4441_, 2, v_k_4322_);
                        leanh::lean_closure_set(v___f_4441_, 3, v___x_4440_);
                        v___x_4442_ = (leanh::lean_unbox(v_fst_4436_) as u8);
                        leanh::lean_dec(v_fst_4436_);
                        v___x_4443_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_fst_4435_, v___x_4442_, v_a_4439_, v___f_4441_, v_kind_4323_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
                        return v___x_4443_;
                    } else {
                        leanh::lean_dec(v_fst_4436_);
                        leanh::lean_dec(v_fst_4435_);
                        leanh::lean_dec_ref(v_acc_4324_);
                        leanh::lean_dec_ref(v_k_4322_);
                        leanh::lean_dec_ref(v_declInfos_4321_);
                        v_a_4444_ = leanh::lean_ctor_get(v___x_4438_, 0);
                        v_isSharedCheck_4451_ =
                            (!leanh::lean_is_exclusive(v___x_4438_)) as u8;
                        if v_isSharedCheck_4451_ == 0 {
                            v___x_4446_ = v___x_4438_;
                            v_isShared_4447_ = v_isSharedCheck_4451_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4444_);
                            leanh::lean_dec(v___x_4438_);
                            v___x_4446_ = leanh::lean_box(0);
                            v_isShared_4447_ = v_isSharedCheck_4451_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_4447_ == 0 {
                    v___x_4449_ = v___x_4446_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
                    v___x_4449_ = v_reuseFailAlloc_4450_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___lam__1(
    mut v_acc_4470_: *mut leanh::LeanObject,
    mut v_declInfos_4471_: *mut leanh::LeanObject,
    mut v_k_4472_: *mut leanh::LeanObject,
    mut v_kind_4473_: u8,
    mut v_x_4474_: *mut leanh::LeanObject,
    mut v___y_4475_: *mut leanh::LeanObject,
    mut v___y_4476_: *mut leanh::LeanObject,
    mut v___y_4477_: *mut leanh::LeanObject,
    mut v___y_4478_: *mut leanh::LeanObject,
    mut v___y_4479_: *mut leanh::LeanObject,
    mut v___y_4480_: *mut leanh::LeanObject,
    mut v___y_4481_: *mut leanh::LeanObject,
    mut v___y_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = lean_array_push(v_acc_4470_, v_x_4474_);
    v___x_4485_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_4471_, v_k_4472_, v_kind_4473_, v___x_4484_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
    return v___x_4485_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19___boxed(
    mut v_declInfos_4486_: *mut leanh::LeanObject,
    mut v_k_4487_: *mut leanh::LeanObject,
    mut v_kind_4488_: *mut leanh::LeanObject,
    mut v_acc_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
    mut v___y_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
    mut v___y_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
    mut v___y_4497_: *mut leanh::LeanObject,
    mut v___y_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_4499_: u8 = 0;
    let mut v_res_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4499_ = (leanh::lean_unbox(v_kind_4488_) as u8);
    v_res_4500_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_4486_, v_k_4487_, v_kind_boxed_4499_, v_acc_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
    leanh::lean_dec(v___y_4497_);
    leanh::lean_dec_ref(v___y_4496_);
    leanh::lean_dec(v___y_4495_);
    leanh::lean_dec_ref(v___y_4494_);
    leanh::lean_dec(v___y_4493_);
    leanh::lean_dec_ref(v___y_4492_);
    leanh::lean_dec(v___y_4491_);
    leanh::lean_dec_ref(v___y_4490_);
    return v_res_4500_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(
    mut v_declInfos_4501_: *mut leanh::LeanObject,
    mut v_k_4502_: *mut leanh::LeanObject,
    mut v_kind_4503_: u8,
    mut v___y_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
    mut v___y_4506_: *mut leanh::LeanObject,
    mut v___y_4507_: *mut leanh::LeanObject,
    mut v___y_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4513_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1;
    v___x_4514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19(v_declInfos_4501_, v_k_4502_, v_kind_4503_, v___x_4513_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
    return v___x_4514_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14___boxed(
    mut v_declInfos_4515_: *mut leanh::LeanObject,
    mut v_k_4516_: *mut leanh::LeanObject,
    mut v_kind_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
    mut v___y_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
    mut v___y_4522_: *mut leanh::LeanObject,
    mut v___y_4523_: *mut leanh::LeanObject,
    mut v___y_4524_: *mut leanh::LeanObject,
    mut v___y_4525_: *mut leanh::LeanObject,
    mut v___y_4526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_4527_: u8 = 0;
    let mut v_res_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4527_ = (leanh::lean_unbox(v_kind_4517_) as u8);
    v_res_4528_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v_declInfos_4515_, v_k_4516_, v_kind_boxed_4527_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
    leanh::lean_dec(v___y_4525_);
    leanh::lean_dec_ref(v___y_4524_);
    leanh::lean_dec(v___y_4523_);
    leanh::lean_dec_ref(v___y_4522_);
    leanh::lean_dec(v___y_4521_);
    leanh::lean_dec_ref(v___y_4520_);
    leanh::lean_dec(v___y_4519_);
    leanh::lean_dec_ref(v___y_4518_);
    return v_res_4528_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(
    mut v_sz_4529_: usize,
    mut v_i_4530_: usize,
    mut v_bs_4531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4532_: u8 = 0;
    let mut v_v_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: usize = 0;
    let mut v___x_4547_: usize = 0;
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4532_ = lean_usize_dec_lt(v_i_4530_, v_sz_4529_);
                if v___x_4532_ == 0 {
                    return v_bs_4531_;
                } else {
                    v_v_4533_ = lean_array_uget(v_bs_4531_, v_i_4530_);
                    v_fst_4534_ = leanh::lean_ctor_get(v_v_4533_, 0);
                    v_snd_4535_ = leanh::lean_ctor_get(v_v_4533_, 1);
                    v_isSharedCheck_4551_ = (!leanh::lean_is_exclusive(v_v_4533_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4537_ = v_v_4533_;
                        v_isShared_4538_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4535_);
                        leanh::lean_inc(v_fst_4534_);
                        leanh::lean_dec(v_v_4533_);
                        v___x_4537_ = leanh::lean_box(0);
                        v_isShared_4538_ = v_isSharedCheck_4551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4539_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4540_ = lean_array_uset(v_bs_4531_, v_i_4530_, v___x_4539_);
                v___x_4541_ = 0;
                v___x_4542_ = leanh::lean_box((v___x_4541_) as usize);
                if v_isShared_4538_ == 0 {
                    leanh::lean_ctor_set(v___x_4537_, 0, v___x_4542_);
                    v___x_4544_ = v___x_4537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4550_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 1, v_snd_4535_);
                    v___x_4544_ = v_reuseFailAlloc_4550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4545_, 0, v_fst_4534_);
                leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                v___x_4546_ = 1usize;
                v___x_4547_ = lean_usize_add(v_i_4530_, v___x_4546_);
                v___x_4548_ = lean_array_uset(v_bs_x27_4540_, v_i_4530_, v___x_4545_);
                v_i_4530_ = v___x_4547_;
                v_bs_4531_ = v___x_4548_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13___boxed(
    mut v_sz_4552_: *mut leanh::LeanObject,
    mut v_i_4553_: *mut leanh::LeanObject,
    mut v_bs_4554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4555_: usize = 0;
    let mut v_i_boxed_4556_: usize = 0;
    let mut v_res_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4555_ = leanh::lean_unbox_usize(v_sz_4552_);
    leanh::lean_dec(v_sz_4552_);
    v_i_boxed_4556_ = leanh::lean_unbox_usize(v_i_4553_);
    leanh::lean_dec(v_i_4553_);
    v_res_4557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_boxed_4555_, v_i_boxed_4556_, v_bs_4554_);
    return v_res_4557_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(
    mut v_declInfos_4558_: *mut leanh::LeanObject,
    mut v_k_4559_: *mut leanh::LeanObject,
    mut v_kind_4560_: u8,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
    mut v___y_4564_: *mut leanh::LeanObject,
    mut v___y_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
    mut v___y_4568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4570_: usize = 0;
    let mut v___x_4571_: usize = 0;
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4570_ = lean_array_size(v_declInfos_4558_);
    v___x_4571_ = 0usize;
    v___x_4572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__13(v_sz_4570_, v___x_4571_, v_declInfos_4558_);
    v___x_4573_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14(v___x_4572_, v_k_4559_, v_kind_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
    return v___x_4573_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8___boxed(
    mut v_declInfos_4574_: *mut leanh::LeanObject,
    mut v_k_4575_: *mut leanh::LeanObject,
    mut v_kind_4576_: *mut leanh::LeanObject,
    mut v___y_4577_: *mut leanh::LeanObject,
    mut v___y_4578_: *mut leanh::LeanObject,
    mut v___y_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_4586_: u8 = 0;
    let mut v_res_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4586_ = (leanh::lean_unbox(v_kind_4576_) as u8);
    v_res_4587_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v_declInfos_4574_, v_k_4575_, v_kind_boxed_4586_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
    leanh::lean_dec(v___y_4584_);
    leanh::lean_dec_ref(v___y_4583_);
    leanh::lean_dec(v___y_4582_);
    leanh::lean_dec_ref(v___y_4581_);
    leanh::lean_dec(v___y_4580_);
    leanh::lean_dec_ref(v___y_4579_);
    leanh::lean_dec(v___y_4578_);
    leanh::lean_dec_ref(v___y_4577_);
    return v_res_4587_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(
    mut v_snd_4588_: *mut leanh::LeanObject,
    mut v_x_4589_: *mut leanh::LeanObject,
    mut v___y_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
    mut v___y_4593_: *mut leanh::LeanObject,
    mut v___y_4594_: *mut leanh::LeanObject,
    mut v___y_4595_: *mut leanh::LeanObject,
    mut v___y_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4599_, 0, v_snd_4588_);
    return v___x_4599_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed(
    mut v_snd_4600_: *mut leanh::LeanObject,
    mut v_x_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
    mut v___y_4605_: *mut leanh::LeanObject,
    mut v___y_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
    mut v___y_4609_: *mut leanh::LeanObject,
    mut v___y_4610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0(v_snd_4600_, v_x_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
    leanh::lean_dec(v___y_4609_);
    leanh::lean_dec_ref(v___y_4608_);
    leanh::lean_dec(v___y_4607_);
    leanh::lean_dec_ref(v___y_4606_);
    leanh::lean_dec(v___y_4605_);
    leanh::lean_dec_ref(v___y_4604_);
    leanh::lean_dec(v___y_4603_);
    leanh::lean_dec_ref(v___y_4602_);
    leanh::lean_dec_ref(v_x_4601_);
    return v_res_4611_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(
    mut v_sz_4612_: usize,
    mut v_i_4613_: usize,
    mut v_bs_4614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4615_: u8 = 0;
    let mut v_v_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4621_: u8 = 0;
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: usize = 0;
    let mut v___x_4628_: usize = 0;
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4615_ = lean_usize_dec_lt(v_i_4613_, v_sz_4612_);
                if v___x_4615_ == 0 {
                    return v_bs_4614_;
                } else {
                    v_v_4616_ = lean_array_uget(v_bs_4614_, v_i_4613_);
                    v_fst_4617_ = leanh::lean_ctor_get(v_v_4616_, 0);
                    v_snd_4618_ = leanh::lean_ctor_get(v_v_4616_, 1);
                    v_isSharedCheck_4632_ = (!leanh::lean_is_exclusive(v_v_4616_)) as u8;
                    if v_isSharedCheck_4632_ == 0 {
                        v___x_4620_ = v_v_4616_;
                        v_isShared_4621_ = v_isSharedCheck_4632_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4618_);
                        leanh::lean_inc(v_fst_4617_);
                        leanh::lean_dec(v_v_4616_);
                        v___x_4620_ = leanh::lean_box(0);
                        v_isShared_4621_ = v_isSharedCheck_4632_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4622_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4623_ = lean_array_uset(v_bs_4614_, v_i_4613_, v___x_4622_);
                v___f_4624_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                leanh::lean_closure_set(v___f_4624_, 0, v_snd_4618_);
                if v_isShared_4621_ == 0 {
                    leanh::lean_ctor_set(v___x_4620_, 1, v___f_4624_);
                    v___x_4626_ = v___x_4620_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_fst_4617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 1, v___f_4624_);
                    v___x_4626_ = v_reuseFailAlloc_4631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4627_ = 1usize;
                v___x_4628_ = lean_usize_add(v_i_4613_, v___x_4627_);
                v___x_4629_ = lean_array_uset(v_bs_x27_4623_, v_i_4613_, v___x_4626_);
                v_i_4613_ = v___x_4628_;
                v_bs_4614_ = v___x_4629_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7___boxed(
    mut v_sz_4633_: *mut leanh::LeanObject,
    mut v_i_4634_: *mut leanh::LeanObject,
    mut v_bs_4635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4636_: usize = 0;
    let mut v_i_boxed_4637_: usize = 0;
    let mut v_res_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4636_ = leanh::lean_unbox_usize(v_sz_4633_);
    leanh::lean_dec(v_sz_4633_);
    v_i_boxed_4637_ = leanh::lean_unbox_usize(v_i_4634_);
    leanh::lean_dec(v_i_4634_);
    v_res_4638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_boxed_4636_, v_i_boxed_4637_, v_bs_4635_);
    return v_res_4638_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(
    mut v_declInfos_4639_: *mut leanh::LeanObject,
    mut v_k_4640_: *mut leanh::LeanObject,
    mut v_kind_4641_: u8,
    mut v___y_4642_: *mut leanh::LeanObject,
    mut v___y_4643_: *mut leanh::LeanObject,
    mut v___y_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4651_: usize = 0;
    let mut v___x_4652_: usize = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4651_ = lean_array_size(v_declInfos_4639_);
    v___x_4652_ = 0usize;
    v___x_4653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__7(v_sz_4651_, v___x_4652_, v_declInfos_4639_);
    v___x_4654_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8(v___x_4653_, v_k_4640_, v_kind_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
    return v___x_4654_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5___boxed(
    mut v_declInfos_4655_: *mut leanh::LeanObject,
    mut v_k_4656_: *mut leanh::LeanObject,
    mut v_kind_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
    mut v___y_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
    mut v___y_4662_: *mut leanh::LeanObject,
    mut v___y_4663_: *mut leanh::LeanObject,
    mut v___y_4664_: *mut leanh::LeanObject,
    mut v___y_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_4667_: u8 = 0;
    let mut v_res_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4667_ = (leanh::lean_unbox(v_kind_4657_) as u8);
    v_res_4668_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_declInfos_4655_, v_k_4656_, v_kind_boxed_4667_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
    leanh::lean_dec(v___y_4665_);
    leanh::lean_dec_ref(v___y_4664_);
    leanh::lean_dec(v___y_4663_);
    leanh::lean_dec_ref(v___y_4662_);
    leanh::lean_dec(v___y_4661_);
    leanh::lean_dec_ref(v___y_4660_);
    leanh::lean_dec(v___y_4659_);
    leanh::lean_dec_ref(v___y_4658_);
    return v_res_4668_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(
    mut v_sz_4669_: usize,
    mut v_i_4670_: usize,
    mut v_bs_4671_: *mut leanh::LeanObject,
    mut v___y_4672_: *mut leanh::LeanObject,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: usize = 0;
    let mut v___x_4685_: usize = 0;
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ = lean_usize_dec_lt(v_i_4670_, v_sz_4669_);
                if v___x_4677_ == 0 {
                    v___x_4678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4678_, 0, v_bs_4671_);
                    return v___x_4678_;
                } else {
                    v_v_4679_ = lean_array_uget_borrowed(v_bs_4671_, v_i_4670_);
                    leanh::lean_inc(v___y_4675_);
                    leanh::lean_inc_ref(v___y_4674_);
                    leanh::lean_inc(v___y_4673_);
                    leanh::lean_inc_ref(v___y_4672_);
                    leanh::lean_inc(v_v_4679_);
                    v___x_4680_ = lean_infer_type(
                        v_v_4679_,
                        v___y_4672_,
                        v___y_4673_,
                        v___y_4674_,
                        v___y_4675_,
                    );
                    if leanh::lean_obj_tag(v___x_4680_) == 0 {
                        v_a_4681_ = leanh::lean_ctor_get(v___x_4680_, 0);
                        leanh::lean_inc(v_a_4681_);
                        leanh::lean_dec_ref_known(v___x_4680_, 1);
                        v___x_4682_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4683_ = lean_array_uset(v_bs_4671_, v_i_4670_, v___x_4682_);
                        v___x_4684_ = 1usize;
                        v___x_4685_ = lean_usize_add(v_i_4670_, v___x_4684_);
                        v___x_4686_ = lean_array_uset(v_bs_x27_4683_, v_i_4670_, v_a_4681_);
                        v_i_4670_ = v___x_4685_;
                        v_bs_4671_ = v___x_4686_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4671_);
                        v_a_4688_ = leanh::lean_ctor_get(v___x_4680_, 0);
                        v_isSharedCheck_4695_ =
                            (!leanh::lean_is_exclusive(v___x_4680_)) as u8;
                        if v_isSharedCheck_4695_ == 0 {
                            v___x_4690_ = v___x_4680_;
                            v_isShared_4691_ = v_isSharedCheck_4695_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4688_);
                            leanh::lean_dec(v___x_4680_);
                            v___x_4690_ = leanh::lean_box(0);
                            v_isShared_4691_ = v_isSharedCheck_4695_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4691_ == 0 {
                    v___x_4693_ = v___x_4690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4688_);
                    v___x_4693_ = v_reuseFailAlloc_4694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3___boxed(
    mut v_sz_4696_: *mut leanh::LeanObject,
    mut v_i_4697_: *mut leanh::LeanObject,
    mut v_bs_4698_: *mut leanh::LeanObject,
    mut v___y_4699_: *mut leanh::LeanObject,
    mut v___y_4700_: *mut leanh::LeanObject,
    mut v___y_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4704_: usize = 0;
    let mut v_i_boxed_4705_: usize = 0;
    let mut v_res_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4704_ = leanh::lean_unbox_usize(v_sz_4696_);
    leanh::lean_dec(v_sz_4696_);
    v_i_boxed_4705_ = leanh::lean_unbox_usize(v_i_4697_);
    leanh::lean_dec(v_i_4697_);
    v_res_4706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_boxed_4704_, v_i_boxed_4705_, v_bs_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
    leanh::lean_dec(v___y_4702_);
    leanh::lean_dec_ref(v___y_4701_);
    leanh::lean_dec(v___y_4700_);
    leanh::lean_dec_ref(v___y_4699_);
    return v_res_4706_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(
    mut v_sz_4707_: usize,
    mut v_i_4708_: usize,
    mut v_bs_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: usize = 0;
    let mut v___x_4725_: usize = 0;
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4731_: u8 = 0;
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4715_ = lean_usize_dec_lt(v_i_4708_, v_sz_4707_);
                if v___x_4715_ == 0 {
                    v___x_4716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4716_, 0, v_bs_4709_);
                    return v___x_4716_;
                } else {
                    v_v_4717_ = lean_array_uget_borrowed(v_bs_4709_, v_i_4708_);
                    v_fst_4718_ = leanh::lean_ctor_get(v_v_4717_, 0);
                    v_snd_4719_ = leanh::lean_ctor_get(v_v_4717_, 1);
                    leanh::lean_inc(v_fst_4718_);
                    leanh::lean_inc(v_snd_4719_);
                    v___x_4720_ = l_Lean_Meta_mkEq(
                        v_snd_4719_,
                        v_fst_4718_,
                        v___y_4710_,
                        v___y_4711_,
                        v___y_4712_,
                        v___y_4713_,
                    );
                    if leanh::lean_obj_tag(v___x_4720_) == 0 {
                        v_a_4721_ = leanh::lean_ctor_get(v___x_4720_, 0);
                        leanh::lean_inc(v_a_4721_);
                        leanh::lean_dec_ref_known(v___x_4720_, 1);
                        v___x_4722_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4723_ = lean_array_uset(v_bs_4709_, v_i_4708_, v___x_4722_);
                        v___x_4724_ = 1usize;
                        v___x_4725_ = lean_usize_add(v_i_4708_, v___x_4724_);
                        v___x_4726_ = lean_array_uset(v_bs_x27_4723_, v_i_4708_, v_a_4721_);
                        v_i_4708_ = v___x_4725_;
                        v_bs_4709_ = v___x_4726_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4709_);
                        v_a_4728_ = leanh::lean_ctor_get(v___x_4720_, 0);
                        v_isSharedCheck_4735_ =
                            (!leanh::lean_is_exclusive(v___x_4720_)) as u8;
                        if v_isSharedCheck_4735_ == 0 {
                            v___x_4730_ = v___x_4720_;
                            v_isShared_4731_ = v_isSharedCheck_4735_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4728_);
                            leanh::lean_dec(v___x_4720_);
                            v___x_4730_ = leanh::lean_box(0);
                            v_isShared_4731_ = v_isSharedCheck_4735_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4731_ == 0 {
                    v___x_4733_ = v___x_4730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
                    v___x_4733_ = v_reuseFailAlloc_4734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg___boxed(
    mut v_sz_4736_: *mut leanh::LeanObject,
    mut v_i_4737_: *mut leanh::LeanObject,
    mut v_bs_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
    mut v___y_4743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4744_: usize = 0;
    let mut v_i_boxed_4745_: usize = 0;
    let mut v_res_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4744_ = leanh::lean_unbox_usize(v_sz_4736_);
    leanh::lean_dec(v_sz_4736_);
    v_i_boxed_4745_ = leanh::lean_unbox_usize(v_i_4737_);
    leanh::lean_dec(v_i_4737_);
    v_res_4746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_boxed_4744_, v_i_boxed_4745_, v_bs_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
    leanh::lean_dec(v___y_4742_);
    leanh::lean_dec_ref(v___y_4741_);
    leanh::lean_dec(v___y_4740_);
    leanh::lean_dec_ref(v___y_4739_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(
    mut v_revertArgs_4747_: *mut leanh::LeanObject,
    mut v_hypName_4748_: *mut leanh::LeanObject,
    mut v_u_4749_: *mut leanh::LeanObject,
    mut v_00_u03c3s_4750_: *mut leanh::LeanObject,
    mut v___x_4751_: u8,
    mut v_hyps_4752_: *mut leanh::LeanObject,
    mut v_ss_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
    mut v___y_4755_: *mut leanh::LeanObject,
    mut v___y_4756_: *mut leanh::LeanObject,
    mut v___y_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
    mut v___y_4760_: *mut leanh::LeanObject,
    mut v___y_4761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4764_: usize = 0;
    let mut v___x_4765_: usize = 0;
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqs_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4781_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c6_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v_a_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut v_a_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4800_: u8 = 0;
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4804_: u8 = 0;
    let mut v_a_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_a_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4816_: u8 = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4763_ = l_Array_zip___redArg(v_revertArgs_4747_, v_ss_4753_);
                v_sz_4764_ = lean_array_size(v___x_4763_);
                v___x_4765_ = 0usize;
                v___x_4766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_4764_, v___x_4765_, v___x_4763_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
                if leanh::lean_obj_tag(v___x_4766_) == 0 {
                    v_a_4767_ = leanh::lean_ctor_get(v___x_4766_, 0);
                    leanh::lean_inc(v_a_4767_);
                    leanh::lean_dec_ref_known(v___x_4766_, 1);
                    leanh::lean_inc(v_hypName_4748_);
                    v___x_4768_ =
                        l_Lean_Core_mkFreshUserName(v_hypName_4748_, v___y_4760_, v___y_4761_);
                    if leanh::lean_obj_tag(v___x_4768_) == 0 {
                        v_a_4769_ = leanh::lean_ctor_get(v___x_4768_, 0);
                        leanh::lean_inc(v_a_4769_);
                        leanh::lean_dec_ref_known(v___x_4768_, 1);
                        v_eqs_4770_ = lean_array_to_list(v_a_4767_);
                        v_00_u03c6_4771_ = l_Lean_mkAndN(v_eqs_4770_);
                        v_00_u03c6_4772_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(
                            v_u_4749_,
                            v_00_u03c3s_4750_,
                            v_00_u03c6_4771_,
                        );
                        v___x_4773_ = 1;
                        v___x_4774_ = 1;
                        v___x_4775_ = l_Lean_Meta_mkLambdaFVars(
                            v_ss_4753_,
                            v_00_u03c6_4772_,
                            v___x_4751_,
                            v___x_4773_,
                            v___x_4751_,
                            v___x_4773_,
                            v___x_4774_,
                            v___y_4758_,
                            v___y_4759_,
                            v___y_4760_,
                            v___y_4761_,
                        );
                        if leanh::lean_obj_tag(v___x_4775_) == 0 {
                            v_a_4776_ = leanh::lean_ctor_get(v___x_4775_, 0);
                            leanh::lean_inc(v_a_4776_);
                            leanh::lean_dec_ref_known(v___x_4775_, 1);
                            v___x_4777_ = l_Lean_Meta_mkLambdaFVars(
                                v_ss_4753_,
                                v_hyps_4752_,
                                v___x_4751_,
                                v___x_4773_,
                                v___x_4751_,
                                v___x_4773_,
                                v___x_4774_,
                                v___y_4758_,
                                v___y_4759_,
                                v___y_4760_,
                                v___y_4761_,
                            );
                            if leanh::lean_obj_tag(v___x_4777_) == 0 {
                                v_a_4778_ = leanh::lean_ctor_get(v___x_4777_, 0);
                                v_isSharedCheck_4788_ =
                                    (!leanh::lean_is_exclusive(v___x_4777_)) as u8;
                                if v_isSharedCheck_4788_ == 0 {
                                    v___x_4780_ = v___x_4777_;
                                    v_isShared_4781_ = v_isSharedCheck_4788_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4778_);
                                    leanh::lean_dec(v___x_4777_);
                                    v___x_4780_ = leanh::lean_box(0);
                                    v_isShared_4781_ = v_isSharedCheck_4788_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_4776_);
                                leanh::lean_dec(v_a_4769_);
                                leanh::lean_dec(v_hypName_4748_);
                                v_a_4789_ = leanh::lean_ctor_get(v___x_4777_, 0);
                                v_isSharedCheck_4796_ =
                                    (!leanh::lean_is_exclusive(v___x_4777_)) as u8;
                                if v_isSharedCheck_4796_ == 0 {
                                    v___x_4791_ = v___x_4777_;
                                    v_isShared_4792_ = v_isSharedCheck_4796_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4789_);
                                    leanh::lean_dec(v___x_4777_);
                                    v___x_4791_ = leanh::lean_box(0);
                                    v_isShared_4792_ = v_isSharedCheck_4796_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4769_);
                            leanh::lean_dec_ref(v_hyps_4752_);
                            leanh::lean_dec(v_hypName_4748_);
                            v_a_4797_ = leanh::lean_ctor_get(v___x_4775_, 0);
                            v_isSharedCheck_4804_ =
                                (!leanh::lean_is_exclusive(v___x_4775_)) as u8;
                            if v_isSharedCheck_4804_ == 0 {
                                v___x_4799_ = v___x_4775_;
                                v_isShared_4800_ = v_isSharedCheck_4804_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4797_);
                                leanh::lean_dec(v___x_4775_);
                                v___x_4799_ = leanh::lean_box(0);
                                v_isShared_4800_ = v_isSharedCheck_4804_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4767_);
                        leanh::lean_dec_ref(v_hyps_4752_);
                        leanh::lean_dec_ref(v_00_u03c3s_4750_);
                        leanh::lean_dec(v_u_4749_);
                        leanh::lean_dec(v_hypName_4748_);
                        v_a_4805_ = leanh::lean_ctor_get(v___x_4768_, 0);
                        v_isSharedCheck_4812_ =
                            (!leanh::lean_is_exclusive(v___x_4768_)) as u8;
                        if v_isSharedCheck_4812_ == 0 {
                            v___x_4807_ = v___x_4768_;
                            v_isShared_4808_ = v_isSharedCheck_4812_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4805_);
                            leanh::lean_dec(v___x_4768_);
                            v___x_4807_ = leanh::lean_box(0);
                            v_isShared_4808_ = v_isSharedCheck_4812_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_hyps_4752_);
                    leanh::lean_dec_ref(v_00_u03c3s_4750_);
                    leanh::lean_dec(v_u_4749_);
                    leanh::lean_dec(v_hypName_4748_);
                    v_a_4813_ = leanh::lean_ctor_get(v___x_4766_, 0);
                    v_isSharedCheck_4820_ = (!leanh::lean_is_exclusive(v___x_4766_)) as u8;
                    if v_isSharedCheck_4820_ == 0 {
                        v___x_4815_ = v___x_4766_;
                        v_isShared_4816_ = v_isSharedCheck_4820_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4813_);
                        leanh::lean_dec(v___x_4766_);
                        v___x_4815_ = leanh::lean_box(0);
                        v_isShared_4816_ = v_isSharedCheck_4820_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4782_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4782_, 0, v_hypName_4748_);
                leanh::lean_ctor_set(v___x_4782_, 1, v_a_4769_);
                leanh::lean_ctor_set(v___x_4782_, 2, v_a_4776_);
                v_00_u03c6_4783_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_4782_);
                v___x_4784_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4784_, 0, v_a_4778_);
                leanh::lean_ctor_set(v___x_4784_, 1, v_00_u03c6_4783_);
                if v_isShared_4781_ == 0 {
                    leanh::lean_ctor_set(v___x_4780_, 0, v___x_4784_);
                    v___x_4786_ = v___x_4780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
                    v___x_4786_ = v_reuseFailAlloc_4787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4786_;
            }
            3 => {
                if v_isShared_4792_ == 0 {
                    v___x_4794_ = v___x_4791_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
                    v___x_4794_ = v_reuseFailAlloc_4795_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4794_;
            }
            5 => {
                if v_isShared_4800_ == 0 {
                    v___x_4802_ = v___x_4799_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
                    v___x_4802_ = v_reuseFailAlloc_4803_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4802_;
            }
            7 => {
                if v_isShared_4808_ == 0 {
                    v___x_4810_ = v___x_4807_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
                    v___x_4810_ = v_reuseFailAlloc_4811_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4810_;
            }
            9 => {
                if v_isShared_4816_ == 0 {
                    v___x_4818_ = v___x_4815_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4819_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
                    v___x_4818_ = v_reuseFailAlloc_4819_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed(
    mut v_revertArgs_4821_: *mut leanh::LeanObject,
    mut v_hypName_4822_: *mut leanh::LeanObject,
    mut v_u_4823_: *mut leanh::LeanObject,
    mut v_00_u03c3s_4824_: *mut leanh::LeanObject,
    mut v___x_4825_: *mut leanh::LeanObject,
    mut v_hyps_4826_: *mut leanh::LeanObject,
    mut v_ss_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
    mut v___y_4831_: *mut leanh::LeanObject,
    mut v___y_4832_: *mut leanh::LeanObject,
    mut v___y_4833_: *mut leanh::LeanObject,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_21499__boxed_4837_: u8 = 0;
    let mut v_res_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_21499__boxed_4837_ = (leanh::lean_unbox(v___x_4825_) as u8);
    v_res_4838_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0(v_revertArgs_4821_, v_hypName_4822_, v_u_4823_, v_00_u03c3s_4824_, v___x_21499__boxed_4837_, v_hyps_4826_, v_ss_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    leanh::lean_dec(v___y_4835_);
    leanh::lean_dec_ref(v___y_4834_);
    leanh::lean_dec(v___y_4833_);
    leanh::lean_dec_ref(v___y_4832_);
    leanh::lean_dec(v___y_4831_);
    leanh::lean_dec_ref(v___y_4830_);
    leanh::lean_dec(v___y_4829_);
    leanh::lean_dec_ref(v___y_4828_);
    leanh::lean_dec_ref(v_ss_4827_);
    leanh::lean_dec_ref(v_revertArgs_4821_);
    return v_res_4838_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(
    mut v_goal_4839_: *mut leanh::LeanObject,
    mut v_n_4840_: *mut leanh::LeanObject,
    mut v_hypName_4841_: *mut leanh::LeanObject,
    mut v_k_4842_: *mut leanh::LeanObject,
    mut v___y_4843_: *mut leanh::LeanObject,
    mut v___y_4844_: *mut leanh::LeanObject,
    mut v___y_4845_: *mut leanh::LeanObject,
    mut v___y_4846_: *mut leanh::LeanObject,
    mut v___y_4847_: *mut leanh::LeanObject,
    mut v___y_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v_u_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v_T_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_revertArgs_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_H_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_x27_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4904_: u8 = 0;
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4918_: u8 = 0;
    let mut v_reuseFailAlloc_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4932_: usize = 0;
    let mut v___x_4933_: usize = 0;
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: u8 = 0;
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: u8 = 0;
    let mut v___x_4951_: usize = 0;
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v_a_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4964_: u8 = 0;
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut v_a_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4976_: u8 = 0;
    let mut v_a_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4984_: u8 = 0;
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4852_ = leanh::lean_unsigned_to_nat(0);
                v___x_4853_ = lean_nat_dec_eq(v_n_4840_, v___x_4852_);
                if v___x_4853_ == 0 {
                    v_u_4854_ = leanh::lean_ctor_get(v_goal_4839_, 0);
                    v_00_u03c3s_4855_ = leanh::lean_ctor_get(v_goal_4839_, 1);
                    v_hyps_4856_ = leanh::lean_ctor_get(v_goal_4839_, 2);
                    v_target_4857_ = leanh::lean_ctor_get(v_goal_4839_, 3);
                    v_isSharedCheck_5011_ = (!leanh::lean_is_exclusive(v_goal_4839_)) as u8;
                    if v_isSharedCheck_5011_ == 0 {
                        v___x_4859_ = v_goal_4839_;
                        v_isShared_4860_ = v_isSharedCheck_5011_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_target_4857_);
                        leanh::lean_inc(v_hyps_4856_);
                        leanh::lean_inc(v_00_u03c3s_4855_);
                        leanh::lean_inc(v_u_4854_);
                        leanh::lean_dec(v_goal_4839_);
                        v___x_4859_ = leanh::lean_box(0);
                        v_isShared_4860_ = v_isSharedCheck_5011_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_hypName_4841_);
                    leanh::lean_dec(v_n_4840_);
                    leanh::lean_inc(v___y_4850_);
                    leanh::lean_inc_ref(v___y_4849_);
                    leanh::lean_inc(v___y_4848_);
                    leanh::lean_inc_ref(v___y_4847_);
                    leanh::lean_inc(v___y_4846_);
                    leanh::lean_inc_ref(v___y_4845_);
                    leanh::lean_inc(v___y_4844_);
                    leanh::lean_inc_ref(v___y_4843_);
                    v___x_5012_ = leanh::lean_apply_10(
                        v_k_4842_,
                        v_goal_4839_,
                        v___y_4843_,
                        v___y_4844_,
                        v___y_4845_,
                        v___y_4846_,
                        v___y_4847_,
                        v___y_4848_,
                        v___y_4849_,
                        v___y_4850_,
                        leanh::lean_box(0),
                    );
                    return v___x_5012_;
                }
            }
            1 => {
                v_T_4861_ = l_Lean_Expr_consumeMData(v_target_4857_);
                v_f_4862_ = l_Lean_Expr_getAppFn(v_T_4861_);
                v___x_4863_ = l_Lean_Expr_getAppNumArgs(v_T_4861_);
                v___x_4864_ = lean_mk_empty_array_with_capacity(v___x_4863_);
                leanh::lean_dec(v___x_4863_);
                leanh::lean_inc_ref(v_T_4861_);
                v_a_4865_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_T_4861_, v___x_4864_);
                leanh::lean_inc(v_n_4840_);
                leanh::lean_inc_ref(v_a_4865_);
                v___x_4866_ = l_Array_toSubarray___redArg(v_a_4865_, v___x_4852_, v_n_4840_);
                v___x_4867_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__1;
                v___x_4868_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v___x_4866_, v___x_4867_);
                v_revertArgs_4869_ = l_Array_reverse___redArg(v___x_4868_);
                v___x_4921_ = leanh::lean_box((v___x_4853_) as usize);
                leanh::lean_inc_ref(v_hyps_4856_);
                leanh::lean_inc_ref(v_00_u03c3s_4855_);
                leanh::lean_inc(v_u_4854_);
                leanh::lean_inc_ref(v_revertArgs_4869_);
                v___f_4922_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___lam__0___boxed as *mut core::ffi::c_void, 16, 6);
                leanh::lean_closure_set(v___f_4922_, 0, v_revertArgs_4869_);
                leanh::lean_closure_set(v___f_4922_, 1, v_hypName_4841_);
                leanh::lean_closure_set(v___f_4922_, 2, v_u_4854_);
                leanh::lean_closure_set(v___f_4922_, 3, v_00_u03c3s_4855_);
                leanh::lean_closure_set(v___f_4922_, 4, v___x_4921_);
                leanh::lean_closure_set(v___f_4922_, 5, v_hyps_4856_);
                v___x_4985_ = lean_array_get_size(v_revertArgs_4869_);
                v___x_4986_ = lean_nat_dec_eq(v___x_4985_, v_n_4840_);
                if v___x_4986_ == 0 {
                    leanh::lean_dec_ref(v___f_4922_);
                    leanh::lean_dec_ref(v_revertArgs_4869_);
                    leanh::lean_dec_ref(v_a_4865_);
                    leanh::lean_dec_ref(v_f_4862_);
                    leanh::lean_del_object(v___x_4859_);
                    leanh::lean_dec_ref(v_target_4857_);
                    leanh::lean_dec_ref(v_hyps_4856_);
                    leanh::lean_dec_ref(v_00_u03c3s_4855_);
                    leanh::lean_dec(v_u_4854_);
                    leanh::lean_dec_ref(v_k_4842_);
                    v___x_4987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__3);
                    v___x_4988_ = l_Nat_reprFast(v_n_4840_);
                    v___x_4989_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4989_, 0, v___x_4988_);
                    v___x_4990_ = l_Lean_MessageData_ofFormat(v___x_4989_);
                    v___x_4991_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4991_, 0, v___x_4987_);
                    leanh::lean_ctor_set(v___x_4991_, 1, v___x_4990_);
                    v___x_4992_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__5);
                    v___x_4993_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4993_, 0, v___x_4991_);
                    leanh::lean_ctor_set(v___x_4993_, 1, v___x_4992_);
                    v___x_4994_ = l_Lean_MessageData_ofExpr(v_T_4861_);
                    v___x_4995_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4995_, 0, v___x_4993_);
                    leanh::lean_ctor_set(v___x_4995_, 1, v___x_4994_);
                    v___x_4996_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___closed__7);
                    v___x_4997_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4997_, 0, v___x_4995_);
                    leanh::lean_ctor_set(v___x_4997_, 1, v___x_4996_);
                    v___x_4998_ = l_Nat_reprFast(v___x_4985_);
                    v___x_4999_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4999_, 0, v___x_4998_);
                    v___x_5000_ = l_Lean_MessageData_ofFormat(v___x_4999_);
                    v___x_5001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5001_, 0, v___x_4997_);
                    leanh::lean_ctor_set(v___x_5001_, 1, v___x_5000_);
                    v___x_5002_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_5001_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
                    v_a_5003_ = leanh::lean_ctor_get(v___x_5002_, 0);
                    v_isSharedCheck_5010_ = (!leanh::lean_is_exclusive(v___x_5002_)) as u8;
                    if v_isSharedCheck_5010_ == 0 {
                        v___x_5005_ = v___x_5002_;
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5003_);
                        leanh::lean_dec(v___x_5002_);
                        v___x_5005_ = leanh::lean_box(0);
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_T_4861_);
                    v___y_4924_ = v___y_4843_;
                    v___y_4925_ = v___y_4844_;
                    v___y_4926_ = v___y_4845_;
                    v___y_4927_ = v___y_4846_;
                    v___y_4928_ = v___y_4847_;
                    v___y_4929_ = v___y_4848_;
                    v___y_4930_ = v___y_4849_;
                    v___y_4931_ = v___y_4850_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                v___x_4883_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___y_4873_, v___y_4880_);
                if leanh::lean_obj_tag(v___x_4883_) == 0 {
                    v_a_4884_ = leanh::lean_ctor_get(v___x_4883_, 0);
                    leanh::lean_inc(v_a_4884_);
                    leanh::lean_dec_ref_known(v___x_4883_, 1);
                    leanh::lean_inc_ref_n(v___y_4882_, 2);
                    v_H_4885_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
                        v___y_4882_,
                        v_a_4884_,
                    );
                    leanh::lean_inc(v_u_4854_);
                    v___x_4886_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                        v_u_4854_,
                        v___y_4882_,
                        v_H_4885_,
                        v___y_4877_,
                    );
                    v_fst_4887_ = leanh::lean_ctor_get(v___x_4886_, 0);
                    v_snd_4888_ = leanh::lean_ctor_get(v___x_4886_, 1);
                    v_isSharedCheck_4920_ = (!leanh::lean_is_exclusive(v___x_4886_)) as u8;
                    if v_isSharedCheck_4920_ == 0 {
                        v___x_4890_ = v___x_4886_;
                        v_isShared_4891_ = v_isSharedCheck_4920_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4888_);
                        leanh::lean_inc(v_fst_4887_);
                        leanh::lean_dec(v___x_4886_);
                        v___x_4890_ = leanh::lean_box(0);
                        v_isShared_4891_ = v_isSharedCheck_4920_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4882_);
                    leanh::lean_dec_ref(v___y_4877_);
                    leanh::lean_dec_ref(v___y_4875_);
                    leanh::lean_dec_ref(v_revertArgs_4869_);
                    leanh::lean_dec_ref(v_a_4865_);
                    leanh::lean_dec_ref(v_f_4862_);
                    leanh::lean_del_object(v___x_4859_);
                    leanh::lean_dec_ref(v_target_4857_);
                    leanh::lean_dec_ref(v_hyps_4856_);
                    leanh::lean_dec_ref(v_00_u03c3s_4855_);
                    leanh::lean_dec(v_u_4854_);
                    leanh::lean_dec_ref(v_k_4842_);
                    leanh::lean_dec(v_n_4840_);
                    return v___x_4883_;
                }
            }
            3 => {
                v___x_4892_ = lean_array_get_size(v_a_4865_);
                v___x_4893_ = l_Array_toSubarray___redArg(v_a_4865_, v_n_4840_, v___x_4892_);
                v___x_4894_ = l_Subarray_copy___redArg(v___x_4893_);
                v___x_4895_ = l_Lean_mkAppRev(v_f_4862_, v___x_4894_);
                leanh::lean_dec_ref(v___x_4894_);
                leanh::lean_inc(v_fst_4887_);
                leanh::lean_inc(v_u_4854_);
                if v_isShared_4860_ == 0 {
                    leanh::lean_ctor_set(v___x_4859_, 3, v___x_4895_);
                    leanh::lean_ctor_set(v___x_4859_, 2, v_fst_4887_);
                    leanh::lean_ctor_set(v___x_4859_, 1, v___y_4882_);
                    v_goal_x27_4897_ = v___x_4859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4919_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_u_4854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 1, v___y_4882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 2, v_fst_4887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 3, v___x_4895_);
                    v_goal_x27_4897_ = v_reuseFailAlloc_4919_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v___y_4874_);
                leanh::lean_inc_ref(v___y_4878_);
                leanh::lean_inc(v___y_4880_);
                leanh::lean_inc_ref(v___y_4871_);
                leanh::lean_inc(v___y_4879_);
                leanh::lean_inc_ref(v___y_4876_);
                leanh::lean_inc(v___y_4881_);
                leanh::lean_inc_ref(v___y_4872_);
                v___x_4898_ = leanh::lean_apply_10(
                    v_k_4842_,
                    v_goal_x27_4897_,
                    v___y_4872_,
                    v___y_4881_,
                    v___y_4876_,
                    v___y_4879_,
                    v___y_4871_,
                    v___y_4880_,
                    v___y_4878_,
                    v___y_4874_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4898_) == 0 {
                    v_a_4899_ = leanh::lean_ctor_get(v___x_4898_, 0);
                    leanh::lean_inc(v_a_4899_);
                    leanh::lean_dec_ref_known(v___x_4898_, 1);
                    leanh::lean_inc(v___y_4874_);
                    leanh::lean_inc_ref(v___y_4878_);
                    leanh::lean_inc(v___y_4880_);
                    leanh::lean_inc_ref(v___y_4871_);
                    leanh::lean_inc_ref(v___y_4875_);
                    v___x_4900_ = lean_infer_type(
                        v___y_4875_,
                        v___y_4871_,
                        v___y_4880_,
                        v___y_4878_,
                        v___y_4874_,
                    );
                    if leanh::lean_obj_tag(v___x_4900_) == 0 {
                        v_a_4901_ = leanh::lean_ctor_get(v___x_4900_, 0);
                        v_isSharedCheck_4918_ =
                            (!leanh::lean_is_exclusive(v___x_4900_)) as u8;
                        if v_isSharedCheck_4918_ == 0 {
                            v___x_4903_ = v___x_4900_;
                            v_isShared_4904_ = v_isSharedCheck_4918_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4901_);
                            leanh::lean_dec(v___x_4900_);
                            v___x_4903_ = leanh::lean_box(0);
                            v_isShared_4904_ = v_isSharedCheck_4918_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4899_);
                        leanh::lean_del_object(v___x_4890_);
                        leanh::lean_dec(v_snd_4888_);
                        leanh::lean_dec(v_fst_4887_);
                        leanh::lean_dec_ref(v___y_4875_);
                        leanh::lean_dec_ref(v_revertArgs_4869_);
                        leanh::lean_dec_ref(v_target_4857_);
                        leanh::lean_dec_ref(v_hyps_4856_);
                        leanh::lean_dec_ref(v_00_u03c3s_4855_);
                        leanh::lean_dec(v_u_4854_);
                        return v___x_4900_;
                    }
                } else {
                    leanh::lean_del_object(v___x_4890_);
                    leanh::lean_dec(v_snd_4888_);
                    leanh::lean_dec(v_fst_4887_);
                    leanh::lean_dec_ref(v___y_4875_);
                    leanh::lean_dec_ref(v_revertArgs_4869_);
                    leanh::lean_dec_ref(v_target_4857_);
                    leanh::lean_dec_ref(v_hyps_4856_);
                    leanh::lean_dec_ref(v_00_u03c3s_4855_);
                    leanh::lean_dec(v_u_4854_);
                    return v___x_4898_;
                }
            }
            5 => {
                v___x_4905_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___redArg___lam__12___closed__1;
                v___x_4906_ = leanh::lean_box(0);
                if v_isShared_4891_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4890_, 1);
                    leanh::lean_ctor_set(v___x_4890_, 1, v___x_4906_);
                    leanh::lean_ctor_set(v___x_4890_, 0, v_u_4854_);
                    v___x_4908_ = v___x_4890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4917_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_u_4854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 1, v___x_4906_);
                    v___x_4908_ = v_reuseFailAlloc_4917_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4909_ = l_Lean_mkConst(v___x_4905_, v___x_4908_);
                v___x_4910_ = l_Lean_mkAppN(v_fst_4887_, v_revertArgs_4869_);
                v___x_4911_ = l_Lean_mkAppN(v_snd_4888_, v_revertArgs_4869_);
                v___x_4912_ = l_Lean_mkAppN(v_a_4899_, v_revertArgs_4869_);
                leanh::lean_dec_ref(v_revertArgs_4869_);
                v_prf_4913_ = l_Lean_mkApp8(
                    v___x_4909_,
                    v_00_u03c3s_4855_,
                    v_a_4901_,
                    v_hyps_4856_,
                    v___x_4910_,
                    v_target_4857_,
                    v___y_4875_,
                    v___x_4911_,
                    v___x_4912_,
                );
                if v_isShared_4904_ == 0 {
                    leanh::lean_ctor_set(v___x_4903_, 0, v_prf_4913_);
                    v___x_4915_ = v___x_4903_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_prf_4913_);
                    v___x_4915_ = v_reuseFailAlloc_4916_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4915_;
            }
            8 => {
                v_sz_4932_ = lean_array_size(v_revertArgs_4869_);
                v___x_4933_ = 0usize;
                leanh::lean_inc_ref(v_revertArgs_4869_);
                v___x_4934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__3(v_sz_4932_, v___x_4933_, v_revertArgs_4869_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
                if leanh::lean_obj_tag(v___x_4934_) == 0 {
                    v_a_4935_ = leanh::lean_ctor_get(v___x_4934_, 0);
                    leanh::lean_inc(v_a_4935_);
                    leanh::lean_dec_ref_known(v___x_4934_, 1);
                    v___x_4936_ = lean_array_get_size(v_a_4935_);
                    v___x_4937_ = lean_mk_empty_array_with_capacity(v___x_4936_);
                    v___x_4938_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_a_4935_, v___x_4936_, v___x_4852_, v___x_4937_, v___y_4930_, v___y_4931_);
                    if leanh::lean_obj_tag(v___x_4938_) == 0 {
                        v_a_4939_ = leanh::lean_ctor_get(v___x_4938_, 0);
                        leanh::lean_inc(v_a_4939_);
                        leanh::lean_dec_ref_known(v___x_4938_, 1);
                        v___x_4940_ = 0;
                        v___x_4941_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5(v_a_4939_, v___f_4922_, v___x_4940_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
                        if leanh::lean_obj_tag(v___x_4941_) == 0 {
                            v_a_4942_ = leanh::lean_ctor_get(v___x_4941_, 0);
                            leanh::lean_inc(v_a_4942_);
                            leanh::lean_dec_ref_known(v___x_4941_, 1);
                            v_fst_4943_ = leanh::lean_ctor_get(v_a_4942_, 0);
                            leanh::lean_inc(v_fst_4943_);
                            v_snd_4944_ = leanh::lean_ctor_get(v_a_4942_, 1);
                            leanh::lean_inc(v_snd_4944_);
                            leanh::lean_dec(v_a_4942_);
                            leanh::lean_inc_ref(v_revertArgs_4869_);
                            v___x_4945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__6(v_sz_4932_, v___x_4933_, v_revertArgs_4869_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
                            if leanh::lean_obj_tag(v___x_4945_) == 0 {
                                v_a_4946_ = leanh::lean_ctor_get(v___x_4945_, 0);
                                leanh::lean_inc(v_a_4946_);
                                leanh::lean_dec_ref_known(v___x_4945_, 1);
                                v___x_4947_ = lean_array_to_list(v_a_4946_);
                                v___x_4948_ = l_Lean_Meta_mkAndIntroN(
                                    v___x_4947_,
                                    v___y_4928_,
                                    v___y_4929_,
                                    v___y_4930_,
                                    v___y_4931_,
                                );
                                if leanh::lean_obj_tag(v___x_4948_) == 0 {
                                    v_a_4949_ = leanh::lean_ctor_get(v___x_4948_, 0);
                                    leanh::lean_inc(v_a_4949_);
                                    leanh::lean_dec_ref_known(v___x_4948_, 1);
                                    v___x_4950_ = lean_nat_dec_lt(v___x_4852_, v___x_4936_);
                                    if v___x_4950_ == 0 {
                                        leanh::lean_dec(v_a_4935_);
                                        leanh::lean_inc_ref(v_00_u03c3s_4855_);
                                        v___y_4871_ = v___y_4928_;
                                        v___y_4872_ = v___y_4924_;
                                        v___y_4873_ = v_fst_4943_;
                                        v___y_4874_ = v___y_4931_;
                                        v___y_4875_ = v_a_4949_;
                                        v___y_4876_ = v___y_4926_;
                                        v___y_4877_ = v_snd_4944_;
                                        v___y_4878_ = v___y_4930_;
                                        v___y_4879_ = v___y_4927_;
                                        v___y_4880_ = v___y_4929_;
                                        v___y_4881_ = v___y_4925_;
                                        v___y_4882_ = v_00_u03c3s_4855_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_4951_ = lean_usize_of_nat(v___x_4936_);
                                        leanh::lean_inc_ref(v_00_u03c3s_4855_);
                                        leanh::lean_inc(v_u_4854_);
                                        v___x_4952_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__7(v_u_4854_, v_a_4935_, v___x_4951_, v___x_4933_, v_00_u03c3s_4855_);
                                        leanh::lean_dec(v_a_4935_);
                                        v___y_4871_ = v___y_4928_;
                                        v___y_4872_ = v___y_4924_;
                                        v___y_4873_ = v_fst_4943_;
                                        v___y_4874_ = v___y_4931_;
                                        v___y_4875_ = v_a_4949_;
                                        v___y_4876_ = v___y_4926_;
                                        v___y_4877_ = v_snd_4944_;
                                        v___y_4878_ = v___y_4930_;
                                        v___y_4879_ = v___y_4927_;
                                        v___y_4880_ = v___y_4929_;
                                        v___y_4881_ = v___y_4925_;
                                        v___y_4882_ = v___x_4952_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_snd_4944_);
                                    leanh::lean_dec(v_fst_4943_);
                                    leanh::lean_dec(v_a_4935_);
                                    leanh::lean_dec_ref(v_revertArgs_4869_);
                                    leanh::lean_dec_ref(v_a_4865_);
                                    leanh::lean_dec_ref(v_f_4862_);
                                    leanh::lean_del_object(v___x_4859_);
                                    leanh::lean_dec_ref(v_target_4857_);
                                    leanh::lean_dec_ref(v_hyps_4856_);
                                    leanh::lean_dec_ref(v_00_u03c3s_4855_);
                                    leanh::lean_dec(v_u_4854_);
                                    leanh::lean_dec_ref(v_k_4842_);
                                    leanh::lean_dec(v_n_4840_);
                                    return v___x_4948_;
                                }
                            } else {
                                leanh::lean_dec(v_snd_4944_);
                                leanh::lean_dec(v_fst_4943_);
                                leanh::lean_dec(v_a_4935_);
                                leanh::lean_dec_ref(v_revertArgs_4869_);
                                leanh::lean_dec_ref(v_a_4865_);
                                leanh::lean_dec_ref(v_f_4862_);
                                leanh::lean_del_object(v___x_4859_);
                                leanh::lean_dec_ref(v_target_4857_);
                                leanh::lean_dec_ref(v_hyps_4856_);
                                leanh::lean_dec_ref(v_00_u03c3s_4855_);
                                leanh::lean_dec(v_u_4854_);
                                leanh::lean_dec_ref(v_k_4842_);
                                leanh::lean_dec(v_n_4840_);
                                v_a_4953_ = leanh::lean_ctor_get(v___x_4945_, 0);
                                v_isSharedCheck_4960_ =
                                    (!leanh::lean_is_exclusive(v___x_4945_)) as u8;
                                if v_isSharedCheck_4960_ == 0 {
                                    v___x_4955_ = v___x_4945_;
                                    v_isShared_4956_ = v_isSharedCheck_4960_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4953_);
                                    leanh::lean_dec(v___x_4945_);
                                    v___x_4955_ = leanh::lean_box(0);
                                    v_isShared_4956_ = v_isSharedCheck_4960_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_4935_);
                            leanh::lean_dec_ref(v_revertArgs_4869_);
                            leanh::lean_dec_ref(v_a_4865_);
                            leanh::lean_dec_ref(v_f_4862_);
                            leanh::lean_del_object(v___x_4859_);
                            leanh::lean_dec_ref(v_target_4857_);
                            leanh::lean_dec_ref(v_hyps_4856_);
                            leanh::lean_dec_ref(v_00_u03c3s_4855_);
                            leanh::lean_dec(v_u_4854_);
                            leanh::lean_dec_ref(v_k_4842_);
                            leanh::lean_dec(v_n_4840_);
                            v_a_4961_ = leanh::lean_ctor_get(v___x_4941_, 0);
                            v_isSharedCheck_4968_ =
                                (!leanh::lean_is_exclusive(v___x_4941_)) as u8;
                            if v_isSharedCheck_4968_ == 0 {
                                v___x_4963_ = v___x_4941_;
                                v_isShared_4964_ = v_isSharedCheck_4968_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4961_);
                                leanh::lean_dec(v___x_4941_);
                                v___x_4963_ = leanh::lean_box(0);
                                v_isShared_4964_ = v_isSharedCheck_4968_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4935_);
                        leanh::lean_dec_ref(v___f_4922_);
                        leanh::lean_dec_ref(v_revertArgs_4869_);
                        leanh::lean_dec_ref(v_a_4865_);
                        leanh::lean_dec_ref(v_f_4862_);
                        leanh::lean_del_object(v___x_4859_);
                        leanh::lean_dec_ref(v_target_4857_);
                        leanh::lean_dec_ref(v_hyps_4856_);
                        leanh::lean_dec_ref(v_00_u03c3s_4855_);
                        leanh::lean_dec(v_u_4854_);
                        leanh::lean_dec_ref(v_k_4842_);
                        leanh::lean_dec(v_n_4840_);
                        v_a_4969_ = leanh::lean_ctor_get(v___x_4938_, 0);
                        v_isSharedCheck_4976_ =
                            (!leanh::lean_is_exclusive(v___x_4938_)) as u8;
                        if v_isSharedCheck_4976_ == 0 {
                            v___x_4971_ = v___x_4938_;
                            v_isShared_4972_ = v_isSharedCheck_4976_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4969_);
                            leanh::lean_dec(v___x_4938_);
                            v___x_4971_ = leanh::lean_box(0);
                            v_isShared_4972_ = v_isSharedCheck_4976_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_4922_);
                    leanh::lean_dec_ref(v_revertArgs_4869_);
                    leanh::lean_dec_ref(v_a_4865_);
                    leanh::lean_dec_ref(v_f_4862_);
                    leanh::lean_del_object(v___x_4859_);
                    leanh::lean_dec_ref(v_target_4857_);
                    leanh::lean_dec_ref(v_hyps_4856_);
                    leanh::lean_dec_ref(v_00_u03c3s_4855_);
                    leanh::lean_dec(v_u_4854_);
                    leanh::lean_dec_ref(v_k_4842_);
                    leanh::lean_dec(v_n_4840_);
                    v_a_4977_ = leanh::lean_ctor_get(v___x_4934_, 0);
                    v_isSharedCheck_4984_ = (!leanh::lean_is_exclusive(v___x_4934_)) as u8;
                    if v_isSharedCheck_4984_ == 0 {
                        v___x_4979_ = v___x_4934_;
                        v_isShared_4980_ = v_isSharedCheck_4984_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4977_);
                        leanh::lean_dec(v___x_4934_);
                        v___x_4979_ = leanh::lean_box(0);
                        v_isShared_4980_ = v_isSharedCheck_4984_;
                        state = 15;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4956_ == 0 {
                    v___x_4958_ = v___x_4955_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4958_;
            }
            11 => {
                if v_isShared_4964_ == 0 {
                    v___x_4966_ = v___x_4963_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
                    v___x_4966_ = v_reuseFailAlloc_4967_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4966_;
            }
            13 => {
                if v_isShared_4972_ == 0 {
                    v___x_4974_ = v___x_4971_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
                    v___x_4974_ = v_reuseFailAlloc_4975_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4974_;
            }
            15 => {
                if v_isShared_4980_ == 0 {
                    v___x_4982_ = v___x_4979_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
                    v___x_4982_ = v_reuseFailAlloc_4983_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4982_;
            }
            17 => {
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1___boxed(
    mut v_goal_5013_: *mut leanh::LeanObject,
    mut v_n_5014_: *mut leanh::LeanObject,
    mut v_hypName_5015_: *mut leanh::LeanObject,
    mut v_k_5016_: *mut leanh::LeanObject,
    mut v___y_5017_: *mut leanh::LeanObject,
    mut v___y_5018_: *mut leanh::LeanObject,
    mut v___y_5019_: *mut leanh::LeanObject,
    mut v___y_5020_: *mut leanh::LeanObject,
    mut v___y_5021_: *mut leanh::LeanObject,
    mut v___y_5022_: *mut leanh::LeanObject,
    mut v___y_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
    mut v___y_5025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5026_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_goal_5013_, v_n_5014_, v_hypName_5015_, v_k_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
    leanh::lean_dec(v___y_5024_);
    leanh::lean_dec_ref(v___y_5023_);
    leanh::lean_dec(v___y_5022_);
    leanh::lean_dec_ref(v___y_5021_);
    leanh::lean_dec(v___y_5020_);
    leanh::lean_dec_ref(v___y_5019_);
    leanh::lean_dec(v___y_5018_);
    leanh::lean_dec_ref(v___y_5017_);
    return v_res_5026_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(
    mut v___x_5030_: *mut leanh::LeanObject,
    mut v_snd_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v_fst_5033_: *mut leanh::LeanObject,
    mut v___y_5034_: *mut leanh::LeanObject,
    mut v___y_5035_: *mut leanh::LeanObject,
    mut v___y_5036_: *mut leanh::LeanObject,
    mut v___y_5037_: *mut leanh::LeanObject,
    mut v___y_5038_: *mut leanh::LeanObject,
    mut v___y_5039_: *mut leanh::LeanObject,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5056_: u8 = 0;
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5060_: u8 = 0;
    let mut v_a_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5064_: u8 = 0;
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5043_ = lean_st_mk_ref(v___x_5030_);
                v___x_5044_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___closed__1;
                v___x_5045_ = l_Lean_Core_mkFreshUserName(v___x_5044_, v___y_5040_, v___y_5041_);
                if leanh::lean_obj_tag(v___x_5045_) == 0 {
                    v_a_5046_ = leanh::lean_ctor_get(v___x_5045_, 0);
                    leanh::lean_inc(v_a_5046_);
                    leanh::lean_dec_ref_known(v___x_5045_, 1);
                    leanh::lean_inc(v___x_5043_);
                    v___f_5047_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5047_, 0, v___x_5043_);
                    v___x_5048_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1(v_snd_5031_, v___y_5032_, v_a_5046_, v___f_5047_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
                    if leanh::lean_obj_tag(v___x_5048_) == 0 {
                        v_a_5049_ = leanh::lean_ctor_get(v___x_5048_, 0);
                        leanh::lean_inc(v_a_5049_);
                        leanh::lean_dec_ref_known(v___x_5048_, 1);
                        v___x_5050_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_fst_5033_, v_a_5049_, v___y_5039_);
                        leanh::lean_dec_ref(v___x_5050_);
                        v___x_5051_ = lean_st_ref_get(v___x_5043_);
                        leanh::lean_dec(v___x_5043_);
                        v___x_5052_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_5051_,
                            v___y_5035_,
                            v___y_5038_,
                            v___y_5039_,
                            v___y_5040_,
                            v___y_5041_,
                        );
                        return v___x_5052_;
                    } else {
                        leanh::lean_dec(v___x_5043_);
                        leanh::lean_dec(v_fst_5033_);
                        v_a_5053_ = leanh::lean_ctor_get(v___x_5048_, 0);
                        v_isSharedCheck_5060_ =
                            (!leanh::lean_is_exclusive(v___x_5048_)) as u8;
                        if v_isSharedCheck_5060_ == 0 {
                            v___x_5055_ = v___x_5048_;
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5053_);
                            leanh::lean_dec(v___x_5048_);
                            v___x_5055_ = leanh::lean_box(0);
                            v_isShared_5056_ = v_isSharedCheck_5060_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5043_);
                    leanh::lean_dec(v_fst_5033_);
                    leanh::lean_dec(v___y_5032_);
                    leanh::lean_dec_ref(v_snd_5031_);
                    v_a_5061_ = leanh::lean_ctor_get(v___x_5045_, 0);
                    v_isSharedCheck_5068_ = (!leanh::lean_is_exclusive(v___x_5045_)) as u8;
                    if v_isSharedCheck_5068_ == 0 {
                        v___x_5063_ = v___x_5045_;
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5061_);
                        leanh::lean_dec(v___x_5045_);
                        v___x_5063_ = leanh::lean_box(0);
                        v_isShared_5064_ = v_isSharedCheck_5068_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5056_ == 0 {
                    v___x_5058_ = v___x_5055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5059_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5053_);
                    v___x_5058_ = v_reuseFailAlloc_5059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5058_;
            }
            3 => {
                if v_isShared_5064_ == 0 {
                    v___x_5066_ = v___x_5063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
                    v___x_5066_ = v_reuseFailAlloc_5067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed(
    mut v___x_5069_: *mut leanh::LeanObject,
    mut v_snd_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
    mut v_fst_5072_: *mut leanh::LeanObject,
    mut v___y_5073_: *mut leanh::LeanObject,
    mut v___y_5074_: *mut leanh::LeanObject,
    mut v___y_5075_: *mut leanh::LeanObject,
    mut v___y_5076_: *mut leanh::LeanObject,
    mut v___y_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
    mut v___y_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5082_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1(
        v___x_5069_,
        v_snd_5070_,
        v___y_5071_,
        v_fst_5072_,
        v___y_5073_,
        v___y_5074_,
        v___y_5075_,
        v___y_5076_,
        v___y_5077_,
        v___y_5078_,
        v___y_5079_,
        v___y_5080_,
    );
    leanh::lean_dec(v___y_5080_);
    leanh::lean_dec_ref(v___y_5079_);
    leanh::lean_dec(v___y_5078_);
    leanh::lean_dec_ref(v___y_5077_);
    leanh::lean_dec(v___y_5076_);
    leanh::lean_dec_ref(v___y_5075_);
    leanh::lean_dec(v___y_5074_);
    leanh::lean_dec_ref(v___y_5073_);
    return v_res_5082_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(
    mut v_goal_5090_: *mut leanh::LeanObject,
    mut v_ref_5091_: *mut leanh::LeanObject,
    mut v_k_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
    mut v___y_5095_: *mut leanh::LeanObject,
    mut v___y_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
    mut v___y_5100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v_p_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5128_: u8 = 0;
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5135_: u8 = 0;
    let mut v_reuseFailAlloc_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5137_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5143_: u8 = 0;
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_goal_5090_);
                v___x_5102_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                    v_goal_5090_,
                    v_ref_5091_,
                    v___y_5097_,
                    v___y_5098_,
                    v___y_5099_,
                    v___y_5100_,
                );
                if leanh::lean_obj_tag(v___x_5102_) == 0 {
                    v_a_5103_ = leanh::lean_ctor_get(v___x_5102_, 0);
                    leanh::lean_inc(v_a_5103_);
                    leanh::lean_dec_ref_known(v___x_5102_, 1);
                    v_focusHyp_5104_ = leanh::lean_ctor_get(v_a_5103_, 0);
                    leanh::lean_inc_ref_n(v_focusHyp_5104_, 2);
                    v_restHyps_5105_ = leanh::lean_ctor_get(v_a_5103_, 1);
                    leanh::lean_inc_ref(v_restHyps_5105_);
                    v_proof_5106_ = leanh::lean_ctor_get(v_a_5103_, 2);
                    leanh::lean_inc_ref(v_proof_5106_);
                    leanh::lean_dec(v_a_5103_);
                    v___x_5107_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_5104_);
                    if leanh::lean_obj_tag(v___x_5107_) == 1 {
                        v_val_5108_ = leanh::lean_ctor_get(v___x_5107_, 0);
                        leanh::lean_inc(v_val_5108_);
                        leanh::lean_dec_ref_known(v___x_5107_, 1);
                        v_u_5109_ = leanh::lean_ctor_get(v_goal_5090_, 0);
                        v_00_u03c3s_5110_ = leanh::lean_ctor_get(v_goal_5090_, 1);
                        v_hyps_5111_ = leanh::lean_ctor_get(v_goal_5090_, 2);
                        v_target_5112_ = leanh::lean_ctor_get(v_goal_5090_, 3);
                        v_isSharedCheck_5137_ =
                            (!leanh::lean_is_exclusive(v_goal_5090_)) as u8;
                        if v_isSharedCheck_5137_ == 0 {
                            v___x_5114_ = v_goal_5090_;
                            v_isShared_5115_ = v_isSharedCheck_5137_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_target_5112_);
                            leanh::lean_inc(v_hyps_5111_);
                            leanh::lean_inc(v_00_u03c3s_5110_);
                            leanh::lean_inc(v_u_5109_);
                            leanh::lean_dec(v_goal_5090_);
                            v___x_5114_ = leanh::lean_box(0);
                            v_isShared_5115_ = v_isSharedCheck_5137_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_5107_);
                        leanh::lean_dec_ref(v_proof_5106_);
                        leanh::lean_dec_ref(v_restHyps_5105_);
                        leanh::lean_dec_ref(v_focusHyp_5104_);
                        leanh::lean_dec_ref(v_k_5092_);
                        leanh::lean_dec_ref(v_goal_5090_);
                        v___x_5138_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__6);
                        v___x_5139_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v___x_5138_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
                        return v___x_5139_;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_5092_);
                    leanh::lean_dec_ref(v_goal_5090_);
                    v_a_5140_ = leanh::lean_ctor_get(v___x_5102_, 0);
                    v_isSharedCheck_5147_ = (!leanh::lean_is_exclusive(v___x_5102_)) as u8;
                    if v_isSharedCheck_5147_ == 0 {
                        v___x_5142_ = v___x_5102_;
                        v_isShared_5143_ = v_isSharedCheck_5147_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5140_);
                        leanh::lean_dec(v___x_5102_);
                        v___x_5142_ = leanh::lean_box(0);
                        v_isShared_5143_ = v_isSharedCheck_5147_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_p_5116_ = leanh::lean_ctor_get(v_val_5108_, 2);
                leanh::lean_inc_ref(v_p_5116_);
                leanh::lean_dec(v_val_5108_);
                v___x_5117_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___redArg___lam__1___closed__4;
                v___x_5118_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_5109_);
                v___x_5119_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5119_, 0, v_u_5109_);
                leanh::lean_ctor_set(v___x_5119_, 1, v___x_5118_);
                leanh::lean_inc_ref(v___x_5119_);
                v___x_5120_ = l_Lean_mkConst(v___x_5117_, v___x_5119_);
                leanh::lean_inc_ref(v_target_5112_);
                leanh::lean_inc_ref_n(v_00_u03c3s_5110_, 2);
                v___x_5121_ =
                    l_Lean_mkApp3(v___x_5120_, v_00_u03c3s_5110_, v_p_5116_, v_target_5112_);
                leanh::lean_inc_ref(v_restHyps_5105_);
                if v_isShared_5115_ == 0 {
                    leanh::lean_ctor_set(v___x_5114_, 3, v___x_5121_);
                    leanh::lean_ctor_set(v___x_5114_, 2, v_restHyps_5105_);
                    v___x_5123_ = v___x_5114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5136_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_u_5109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 1, v_00_u03c3s_5110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 2, v_restHyps_5105_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5136_, 3, v___x_5121_);
                    v___x_5123_ = v_reuseFailAlloc_5136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_5100_);
                leanh::lean_inc_ref(v___y_5099_);
                leanh::lean_inc(v___y_5098_);
                leanh::lean_inc_ref(v___y_5097_);
                leanh::lean_inc(v___y_5096_);
                leanh::lean_inc_ref(v___y_5095_);
                leanh::lean_inc(v___y_5094_);
                leanh::lean_inc_ref(v___y_5093_);
                v___x_5124_ = leanh::lean_apply_10(
                    v_k_5092_,
                    v___x_5123_,
                    v___y_5093_,
                    v___y_5094_,
                    v___y_5095_,
                    v___y_5096_,
                    v___y_5097_,
                    v___y_5098_,
                    v___y_5099_,
                    v___y_5100_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5124_) == 0 {
                    v_a_5125_ = leanh::lean_ctor_get(v___x_5124_, 0);
                    v_isSharedCheck_5135_ = (!leanh::lean_is_exclusive(v___x_5124_)) as u8;
                    if v_isSharedCheck_5135_ == 0 {
                        v___x_5127_ = v___x_5124_;
                        v_isShared_5128_ = v_isSharedCheck_5135_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5125_);
                        leanh::lean_dec(v___x_5124_);
                        v___x_5127_ = leanh::lean_box(0);
                        v_isShared_5128_ = v_isSharedCheck_5135_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5119_, 2);
                    leanh::lean_dec_ref(v_target_5112_);
                    leanh::lean_dec_ref(v_hyps_5111_);
                    leanh::lean_dec_ref(v_00_u03c3s_5110_);
                    leanh::lean_dec_ref(v_proof_5106_);
                    leanh::lean_dec_ref(v_restHyps_5105_);
                    leanh::lean_dec_ref(v_focusHyp_5104_);
                    return v___x_5124_;
                }
            }
            3 => {
                v___x_5129_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___closed__0;
                v___x_5130_ = l_Lean_mkConst(v___x_5129_, v___x_5119_);
                v_prf_5131_ = l_Lean_mkApp7(
                    v___x_5130_,
                    v_00_u03c3s_5110_,
                    v_hyps_5111_,
                    v_restHyps_5105_,
                    v_focusHyp_5104_,
                    v_target_5112_,
                    v_proof_5106_,
                    v_a_5125_,
                );
                if v_isShared_5128_ == 0 {
                    leanh::lean_ctor_set(v___x_5127_, 0, v_prf_5131_);
                    v___x_5133_ = v___x_5127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_prf_5131_);
                    v___x_5133_ = v_reuseFailAlloc_5134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5133_;
            }
            5 => {
                if v_isShared_5143_ == 0 {
                    v___x_5145_ = v___x_5142_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
                    v___x_5145_ = v_reuseFailAlloc_5146_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4___boxed(
    mut v_goal_5148_: *mut leanh::LeanObject,
    mut v_ref_5149_: *mut leanh::LeanObject,
    mut v_k_5150_: *mut leanh::LeanObject,
    mut v___y_5151_: *mut leanh::LeanObject,
    mut v___y_5152_: *mut leanh::LeanObject,
    mut v___y_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
    mut v___y_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5160_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_goal_5148_, v_ref_5149_, v_k_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_);
    leanh::lean_dec(v___y_5158_);
    leanh::lean_dec_ref(v___y_5157_);
    leanh::lean_dec(v___y_5156_);
    leanh::lean_dec_ref(v___y_5155_);
    leanh::lean_dec(v___y_5154_);
    leanh::lean_dec_ref(v___y_5153_);
    leanh::lean_dec(v___y_5152_);
    leanh::lean_dec_ref(v___y_5151_);
    return v_res_5160_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(
    mut v___x_5161_: *mut leanh::LeanObject,
    mut v_val_5162_: *mut leanh::LeanObject,
    mut v_h_5163_: *mut leanh::LeanObject,
    mut v_a_5164_: *mut leanh::LeanObject,
    mut v___y_5165_: *mut leanh::LeanObject,
    mut v___y_5166_: *mut leanh::LeanObject,
    mut v___y_5167_: *mut leanh::LeanObject,
    mut v___y_5168_: *mut leanh::LeanObject,
    mut v___y_5169_: *mut leanh::LeanObject,
    mut v___y_5170_: *mut leanh::LeanObject,
    mut v___y_5171_: *mut leanh::LeanObject,
    mut v___y_5172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5174_ = lean_st_mk_ref(v___x_5161_);
                leanh::lean_inc(v___x_5174_);
                v___f_5175_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    1,
                );
                leanh::lean_closure_set(v___f_5175_, 0, v___x_5174_);
                v___x_5176_ = l_Lean_Elab_Tactic_Do_ProofMode_mRevert___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__4(v_val_5162_, v_h_5163_, v___f_5175_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
                if leanh::lean_obj_tag(v___x_5176_) == 0 {
                    v_a_5177_ = leanh::lean_ctor_get(v___x_5176_, 0);
                    leanh::lean_inc(v_a_5177_);
                    leanh::lean_dec_ref_known(v___x_5176_, 1);
                    v___x_5178_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(v_a_5164_, v_a_5177_, v___y_5170_);
                    leanh::lean_dec_ref(v___x_5178_);
                    v___x_5179_ = lean_st_ref_get(v___x_5174_);
                    leanh::lean_dec(v___x_5174_);
                    v___x_5180_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_5179_,
                        v___y_5166_,
                        v___y_5169_,
                        v___y_5170_,
                        v___y_5171_,
                        v___y_5172_,
                    );
                    return v___x_5180_;
                } else {
                    leanh::lean_dec(v___x_5174_);
                    leanh::lean_dec(v_a_5164_);
                    v_a_5181_ = leanh::lean_ctor_get(v___x_5176_, 0);
                    v_isSharedCheck_5188_ = (!leanh::lean_is_exclusive(v___x_5176_)) as u8;
                    if v_isSharedCheck_5188_ == 0 {
                        v___x_5183_ = v___x_5176_;
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5181_);
                        leanh::lean_dec(v___x_5176_);
                        v___x_5183_ = leanh::lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5184_ == 0 {
                    v___x_5186_ = v___x_5183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed(
    mut v___x_5189_: *mut leanh::LeanObject,
    mut v_val_5190_: *mut leanh::LeanObject,
    mut v_h_5191_: *mut leanh::LeanObject,
    mut v_a_5192_: *mut leanh::LeanObject,
    mut v___y_5193_: *mut leanh::LeanObject,
    mut v___y_5194_: *mut leanh::LeanObject,
    mut v___y_5195_: *mut leanh::LeanObject,
    mut v___y_5196_: *mut leanh::LeanObject,
    mut v___y_5197_: *mut leanh::LeanObject,
    mut v___y_5198_: *mut leanh::LeanObject,
    mut v___y_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5202_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3(
        v___x_5189_,
        v_val_5190_,
        v_h_5191_,
        v_a_5192_,
        v___y_5193_,
        v___y_5194_,
        v___y_5195_,
        v___y_5196_,
        v___y_5197_,
        v___y_5198_,
        v___y_5199_,
        v___y_5200_,
    );
    leanh::lean_dec(v___y_5200_);
    leanh::lean_dec_ref(v___y_5199_);
    leanh::lean_dec(v___y_5198_);
    leanh::lean_dec_ref(v___y_5197_);
    leanh::lean_dec(v___y_5196_);
    leanh::lean_dec_ref(v___y_5195_);
    leanh::lean_dec(v___y_5194_);
    leanh::lean_dec_ref(v___y_5193_);
    return v_res_5202_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(
    mut v_msg_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5209_ = leanh::lean_ctor_get(v___y_5206_, 5);
                v___x_5210_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5_spec__14(v_msg_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
                v_a_5211_ = leanh::lean_ctor_get(v___x_5210_, 0);
                v_isSharedCheck_5219_ = (!leanh::lean_is_exclusive(v___x_5210_)) as u8;
                if v_isSharedCheck_5219_ == 0 {
                    v___x_5213_ = v___x_5210_;
                    v_isShared_5214_ = v_isSharedCheck_5219_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5211_);
                    leanh::lean_dec(v___x_5210_);
                    v___x_5213_ = leanh::lean_box(0);
                    v_isShared_5214_ = v_isSharedCheck_5219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5209_);
                v___x_5215_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5215_, 0, v_ref_5209_);
                leanh::lean_ctor_set(v___x_5215_, 1, v_a_5211_);
                if v_isShared_5214_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5213_, 1);
                    leanh::lean_ctor_set(v___x_5213_, 0, v___x_5215_);
                    v___x_5217_ = v___x_5213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5218_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
                    v___x_5217_ = v_reuseFailAlloc_5218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg___boxed(
    mut v_msg_5220_: *mut leanh::LeanObject,
    mut v___y_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
    mut v___y_5225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5226_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(
            v_msg_5220_,
            v___y_5221_,
            v___y_5222_,
            v___y_5223_,
            v___y_5224_,
        );
    leanh::lean_dec(v___y_5224_);
    leanh::lean_dec_ref(v___y_5223_);
    leanh::lean_dec(v___y_5222_);
    leanh::lean_dec_ref(v___y_5221_);
    return v_res_5226_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__10;
    v___x_5252_ = l_Lean_stringToMessageData(v___x_5251_);
    return v___x_5252_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(
    mut v_x_5253_: *mut leanh::LeanObject,
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_a_5257_: *mut leanh::LeanObject,
    mut v_a_5258_: *mut leanh::LeanObject,
    mut v_a_5259_: *mut leanh::LeanObject,
    mut v_a_5260_: *mut leanh::LeanObject,
    mut v_a_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5303_: u8 = 0;
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: u8 = 0;
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: u8 = 0;
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: u8 = 0;
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v___x_5320_: u8 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_a_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5351_: u8 = 0;
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5278_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3;
                leanh::lean_inc(v_x_5253_);
                v___x_5279_ = l_Lean_Syntax_isOfKind(v_x_5253_, v___x_5278_);
                if v___x_5279_ == 0 {
                    leanh::lean_dec(v_x_5253_);
                    v___x_5280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
                    return v___x_5280_;
                } else {
                    v___x_5281_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5308_ = l_Lean_Syntax_getArg(v_x_5253_, v___x_5281_);
                    leanh::lean_dec(v_x_5253_);
                    leanh::lean_inc(v___x_5308_);
                    v___x_5309_ = l_Lean_Syntax_matchesNull(v___x_5308_, v___x_5281_);
                    if v___x_5309_ == 0 {
                        leanh::lean_dec(v___x_5308_);
                        v___x_5310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
                        return v___x_5310_;
                    } else {
                        v___x_5311_ = leanh::lean_unsigned_to_nat(0);
                        v___x_5312_ = l_Lean_Syntax_getArg(v___x_5308_, v___x_5311_);
                        leanh::lean_dec(v___x_5308_);
                        v___x_5313_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__5;
                        leanh::lean_inc(v___x_5312_);
                        v___x_5314_ = l_Lean_Syntax_isOfKind(v___x_5312_, v___x_5313_);
                        if v___x_5314_ == 0 {
                            v___x_5315_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__7;
                            leanh::lean_inc(v___x_5312_);
                            v___x_5316_ = l_Lean_Syntax_isOfKind(v___x_5312_, v___x_5315_);
                            if v___x_5316_ == 0 {
                                leanh::lean_dec(v___x_5312_);
                                v___x_5317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
                                return v___x_5317_;
                            } else {
                                v___x_5318_ = l_Lean_Syntax_getArg(v___x_5312_, v___x_5281_);
                                leanh::lean_dec(v___x_5312_);
                                v___x_5319_ = l_Lean_Syntax_isNone(v___x_5318_);
                                if v___x_5319_ == 0 {
                                    leanh::lean_inc(v___x_5318_);
                                    v___x_5320_ =
                                        l_Lean_Syntax_matchesNull(v___x_5318_, v___x_5281_);
                                    if v___x_5320_ == 0 {
                                        leanh::lean_dec(v___x_5318_);
                                        v___x_5321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
                                        return v___x_5321_;
                                    } else {
                                        v_n_5322_ = l_Lean_Syntax_getArg(v___x_5318_, v___x_5311_);
                                        leanh::lean_dec(v___x_5318_);
                                        v___x_5323_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_5323_, 0, v_n_5322_);
                                        v_n_5283_ = v___x_5323_;
                                        v___y_5284_ = v_a_5254_;
                                        v___y_5285_ = v_a_5255_;
                                        v___y_5286_ = v_a_5256_;
                                        v___y_5287_ = v_a_5257_;
                                        v___y_5288_ = v_a_5258_;
                                        v___y_5289_ = v_a_5259_;
                                        v___y_5290_ = v_a_5260_;
                                        v___y_5291_ = v_a_5261_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_5318_);
                                    v___x_5324_ = leanh::lean_box(0);
                                    v_n_5283_ = v___x_5324_;
                                    v___y_5284_ = v_a_5254_;
                                    v___y_5285_ = v_a_5255_;
                                    v___y_5286_ = v_a_5256_;
                                    v___y_5287_ = v_a_5257_;
                                    v___y_5288_ = v_a_5258_;
                                    v___y_5289_ = v_a_5259_;
                                    v___y_5290_ = v_a_5260_;
                                    v___y_5291_ = v_a_5261_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v_h_5325_ = l_Lean_Syntax_getArg(v___x_5312_, v___x_5311_);
                            leanh::lean_dec(v___x_5312_);
                            v___x_5326_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__9;
                            leanh::lean_inc(v_h_5325_);
                            v___x_5327_ = l_Lean_Syntax_isOfKind(v_h_5325_, v___x_5326_);
                            if v___x_5327_ == 0 {
                                leanh::lean_dec(v_h_5325_);
                                v___x_5328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__0___redArg();
                                return v___x_5328_;
                            } else {
                                v___x_5329_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                    v_a_5255_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_,
                                );
                                if leanh::lean_obj_tag(v___x_5329_) == 0 {
                                    v_a_5330_ = leanh::lean_ctor_get(v___x_5329_, 0);
                                    leanh::lean_inc_n(v_a_5330_, 2);
                                    leanh::lean_dec_ref_known(v___x_5329_, 1);
                                    v___x_5331_ = l_Lean_MVarId_getType(
                                        v_a_5330_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_,
                                    );
                                    if leanh::lean_obj_tag(v___x_5331_) == 0 {
                                        v_a_5332_ = leanh::lean_ctor_get(v___x_5331_, 0);
                                        leanh::lean_inc(v_a_5332_);
                                        leanh::lean_dec_ref_known(v___x_5331_, 1);
                                        v___x_5333_ =
                                            l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(
                                                v_a_5332_,
                                            );
                                        leanh::lean_dec(v_a_5332_);
                                        if leanh::lean_obj_tag(v___x_5333_) == 1 {
                                            v_val_5334_ =
                                                leanh::lean_ctor_get(v___x_5333_, 0);
                                            leanh::lean_inc(v_val_5334_);
                                            leanh::lean_dec_ref_known(v___x_5333_, 1);
                                            v___x_5335_ = leanh::lean_box(0);
                                            leanh::lean_inc(v_a_5330_);
                                            v___f_5336_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__3___boxed as *mut core::ffi::c_void, 13, 4);
                                            leanh::lean_closure_set(
                                                v___f_5336_,
                                                0,
                                                v___x_5335_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_5336_,
                                                1,
                                                v_val_5334_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_5336_,
                                                2,
                                                v_h_5325_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_5336_,
                                                3,
                                                v_a_5330_,
                                            );
                                            v___x_5337_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v_a_5330_, v___f_5336_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
                                            return v___x_5337_;
                                        } else {
                                            leanh::lean_dec(v___x_5333_);
                                            leanh::lean_dec(v_a_5330_);
                                            leanh::lean_dec(v_h_5325_);
                                            v___x_5338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__11);
                                            v___x_5339_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(v___x_5338_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
                                            return v___x_5339_;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_5330_);
                                        leanh::lean_dec(v_h_5325_);
                                        v_a_5340_ = leanh::lean_ctor_get(v___x_5331_, 0);
                                        v_isSharedCheck_5347_ =
                                            (!leanh::lean_is_exclusive(v___x_5331_)) as u8;
                                        if v_isSharedCheck_5347_ == 0 {
                                            v___x_5342_ = v___x_5331_;
                                            v_isShared_5343_ = v_isSharedCheck_5347_;
                                            state = 5;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5340_);
                                            leanh::lean_dec(v___x_5331_);
                                            v___x_5342_ = leanh::lean_box(0);
                                            v_isShared_5343_ = v_isSharedCheck_5347_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_h_5325_);
                                    v_a_5348_ = leanh::lean_ctor_get(v___x_5329_, 0);
                                    v_isSharedCheck_5355_ =
                                        (!leanh::lean_is_exclusive(v___x_5329_)) as u8;
                                    if v_isSharedCheck_5355_ == 0 {
                                        v___x_5350_ = v___x_5329_;
                                        v_isShared_5351_ = v_isSharedCheck_5355_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5348_);
                                        leanh::lean_dec(v___x_5329_);
                                        v___x_5350_ = leanh::lean_box(0);
                                        v_isShared_5351_ = v_isSharedCheck_5355_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5275_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_5264_);
                v___f_5276_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___lam__1___boxed
                        as *mut core::ffi::c_void,
                    13,
                    4,
                );
                leanh::lean_closure_set(v___f_5276_, 0, v___x_5275_);
                leanh::lean_closure_set(v___f_5276_, 1, v___y_5265_);
                leanh::lean_closure_set(v___f_5276_, 2, v___y_5274_);
                leanh::lean_closure_set(v___f_5276_, 3, v___y_5264_);
                v___x_5277_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__3___redArg(v___y_5264_, v___f_5276_, v___y_5269_, v___y_5266_, v___y_5270_, v___y_5271_, v___y_5267_, v___y_5273_, v___y_5272_, v___y_5268_);
                return v___x_5277_;
            }
            2 => {
                v___x_5292_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                    v___y_5285_,
                    v___y_5288_,
                    v___y_5289_,
                    v___y_5290_,
                    v___y_5291_,
                );
                if leanh::lean_obj_tag(v___x_5292_) == 0 {
                    v_a_5293_ = leanh::lean_ctor_get(v___x_5292_, 0);
                    leanh::lean_inc(v_a_5293_);
                    leanh::lean_dec_ref_known(v___x_5292_, 1);
                    if leanh::lean_obj_tag(v_n_5283_) == 0 {
                        v_fst_5294_ = leanh::lean_ctor_get(v_a_5293_, 0);
                        leanh::lean_inc(v_fst_5294_);
                        v_snd_5295_ = leanh::lean_ctor_get(v_a_5293_, 1);
                        leanh::lean_inc(v_snd_5295_);
                        leanh::lean_dec(v_a_5293_);
                        v___y_5264_ = v_fst_5294_;
                        v___y_5265_ = v_snd_5295_;
                        v___y_5266_ = v___y_5285_;
                        v___y_5267_ = v___y_5288_;
                        v___y_5268_ = v___y_5291_;
                        v___y_5269_ = v___y_5284_;
                        v___y_5270_ = v___y_5286_;
                        v___y_5271_ = v___y_5287_;
                        v___y_5272_ = v___y_5290_;
                        v___y_5273_ = v___y_5289_;
                        v___y_5274_ = v___x_5281_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_5296_ = leanh::lean_ctor_get(v_a_5293_, 0);
                        leanh::lean_inc(v_fst_5296_);
                        v_snd_5297_ = leanh::lean_ctor_get(v_a_5293_, 1);
                        leanh::lean_inc(v_snd_5297_);
                        leanh::lean_dec(v_a_5293_);
                        v_val_5298_ = leanh::lean_ctor_get(v_n_5283_, 0);
                        leanh::lean_inc(v_val_5298_);
                        leanh::lean_dec_ref_known(v_n_5283_, 1);
                        v___x_5299_ = l_Lean_TSyntax_getNat(v_val_5298_);
                        leanh::lean_dec(v_val_5298_);
                        v___y_5264_ = v_fst_5296_;
                        v___y_5265_ = v_snd_5297_;
                        v___y_5266_ = v___y_5285_;
                        v___y_5267_ = v___y_5288_;
                        v___y_5268_ = v___y_5291_;
                        v___y_5269_ = v___y_5284_;
                        v___y_5270_ = v___y_5286_;
                        v___y_5271_ = v___y_5287_;
                        v___y_5272_ = v___y_5290_;
                        v___y_5273_ = v___y_5289_;
                        v___y_5274_ = v___x_5299_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_n_5283_);
                    v_a_5300_ = leanh::lean_ctor_get(v___x_5292_, 0);
                    v_isSharedCheck_5307_ = (!leanh::lean_is_exclusive(v___x_5292_)) as u8;
                    if v_isSharedCheck_5307_ == 0 {
                        v___x_5302_ = v___x_5292_;
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5300_);
                        leanh::lean_dec(v___x_5292_);
                        v___x_5302_ = leanh::lean_box(0);
                        v_isShared_5303_ = v_isSharedCheck_5307_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5303_ == 0 {
                    v___x_5305_ = v___x_5302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
                    v___x_5305_ = v_reuseFailAlloc_5306_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5305_;
            }
            5 => {
                if v_isShared_5343_ == 0 {
                    v___x_5345_ = v___x_5342_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5345_;
            }
            7 => {
                if v_isShared_5351_ == 0 {
                    v___x_5353_ = v___x_5350_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5348_);
                    v___x_5353_ = v_reuseFailAlloc_5354_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed(
    mut v_x_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert(
        v_x_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_, v_a_5362_, v_a_5363_,
        v_a_5364_,
    );
    leanh::lean_dec(v_a_5364_);
    leanh::lean_dec_ref(v_a_5363_);
    leanh::lean_dec(v_a_5362_);
    leanh::lean_dec_ref(v_a_5361_);
    leanh::lean_dec(v_a_5360_);
    leanh::lean_dec_ref(v_a_5359_);
    leanh::lean_dec(v_a_5358_);
    leanh::lean_dec_ref(v_a_5357_);
    return v_res_5366_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(
    mut v_mvarId_5367_: *mut leanh::LeanObject,
    mut v_val_5368_: *mut leanh::LeanObject,
    mut v___y_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5378_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___redArg(
            v_mvarId_5367_,
            v_val_5368_,
            v___y_5374_,
        );
    return v___x_5378_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2___boxed(
    mut v_mvarId_5379_: *mut leanh::LeanObject,
    mut v_val_5380_: *mut leanh::LeanObject,
    mut v___y_5381_: *mut leanh::LeanObject,
    mut v___y_5382_: *mut leanh::LeanObject,
    mut v___y_5383_: *mut leanh::LeanObject,
    mut v___y_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
    mut v___y_5386_: *mut leanh::LeanObject,
    mut v___y_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
    mut v___y_5389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5390_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2(
        v_mvarId_5379_,
        v_val_5380_,
        v___y_5381_,
        v___y_5382_,
        v___y_5383_,
        v___y_5384_,
        v___y_5385_,
        v___y_5386_,
        v___y_5387_,
        v___y_5388_,
    );
    leanh::lean_dec(v___y_5388_);
    leanh::lean_dec_ref(v___y_5387_);
    leanh::lean_dec(v___y_5386_);
    leanh::lean_dec_ref(v___y_5385_);
    leanh::lean_dec(v___y_5384_);
    leanh::lean_dec_ref(v___y_5383_);
    leanh::lean_dec(v___y_5382_);
    leanh::lean_dec_ref(v___y_5381_);
    return v_res_5390_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(
    mut v_00_u03b1_5391_: *mut leanh::LeanObject,
    mut v_msg_5392_: *mut leanh::LeanObject,
    mut v___y_5393_: *mut leanh::LeanObject,
    mut v___y_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
    mut v___y_5396_: *mut leanh::LeanObject,
    mut v___y_5397_: *mut leanh::LeanObject,
    mut v___y_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
    mut v___y_5400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5402_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___redArg(
            v_msg_5392_,
            v___y_5397_,
            v___y_5398_,
            v___y_5399_,
            v___y_5400_,
        );
    return v___x_5402_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5___boxed(
    mut v_00_u03b1_5403_: *mut leanh::LeanObject,
    mut v_msg_5404_: *mut leanh::LeanObject,
    mut v___y_5405_: *mut leanh::LeanObject,
    mut v___y_5406_: *mut leanh::LeanObject,
    mut v___y_5407_: *mut leanh::LeanObject,
    mut v___y_5408_: *mut leanh::LeanObject,
    mut v___y_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
    mut v___y_5411_: *mut leanh::LeanObject,
    mut v___y_5412_: *mut leanh::LeanObject,
    mut v___y_5413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5414_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__5(
        v_00_u03b1_5403_,
        v_msg_5404_,
        v___y_5405_,
        v___y_5406_,
        v___y_5407_,
        v___y_5408_,
        v___y_5409_,
        v___y_5410_,
        v___y_5411_,
        v___y_5412_,
    );
    leanh::lean_dec(v___y_5412_);
    leanh::lean_dec_ref(v___y_5411_);
    leanh::lean_dec(v___y_5410_);
    leanh::lean_dec_ref(v___y_5409_);
    leanh::lean_dec(v___y_5408_);
    leanh::lean_dec_ref(v___y_5407_);
    leanh::lean_dec(v___y_5406_);
    leanh::lean_dec_ref(v___y_5405_);
    return v_res_5414_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1(
    mut v_inst_5415_: *mut leanh::LeanObject,
    mut v_R_5416_: *mut leanh::LeanObject,
    mut v_a_5417_: *mut leanh::LeanObject,
    mut v_b_5418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__1___redArg(v_a_5417_, v_b_5418_);
    return v___x_5419_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(
    mut v_sz_5420_: usize,
    mut v_i_5421_: usize,
    mut v_bs_5422_: *mut leanh::LeanObject,
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
    v___x_5432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___redArg(v_sz_5420_, v_i_5421_, v_bs_5422_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
    return v___x_5432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2___boxed(
    mut v_sz_5433_: *mut leanh::LeanObject,
    mut v_i_5434_: *mut leanh::LeanObject,
    mut v_bs_5435_: *mut leanh::LeanObject,
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
    let mut v_sz_boxed_5445_: usize = 0;
    let mut v_i_boxed_5446_: usize = 0;
    let mut v_res_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5445_ = leanh::lean_unbox_usize(v_sz_5433_);
    leanh::lean_dec(v_sz_5433_);
    v_i_boxed_5446_ = leanh::lean_unbox_usize(v_i_5434_);
    leanh::lean_dec(v_i_5434_);
    v_res_5447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__2(v_sz_boxed_5445_, v_i_boxed_5446_, v_bs_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
    leanh::lean_dec(v___y_5443_);
    leanh::lean_dec_ref(v___y_5442_);
    leanh::lean_dec(v___y_5441_);
    leanh::lean_dec_ref(v___y_5440_);
    leanh::lean_dec(v___y_5439_);
    leanh::lean_dec_ref(v___y_5438_);
    leanh::lean_dec(v___y_5437_);
    leanh::lean_dec_ref(v___y_5436_);
    return v_res_5447_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(
    mut v_as_5448_: *mut leanh::LeanObject,
    mut v_i_5449_: *mut leanh::LeanObject,
    mut v_j_5450_: *mut leanh::LeanObject,
    mut v_inv_5451_: *mut leanh::LeanObject,
    mut v_bs_5452_: *mut leanh::LeanObject,
    mut v___y_5453_: *mut leanh::LeanObject,
    mut v___y_5454_: *mut leanh::LeanObject,
    mut v___y_5455_: *mut leanh::LeanObject,
    mut v___y_5456_: *mut leanh::LeanObject,
    mut v___y_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
    mut v___y_5460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5462_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___redArg(v_as_5448_, v_i_5449_, v_j_5450_, v_bs_5452_, v___y_5459_, v___y_5460_);
    return v___x_5462_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4___boxed(
    mut v_as_5463_: *mut leanh::LeanObject,
    mut v_i_5464_: *mut leanh::LeanObject,
    mut v_j_5465_: *mut leanh::LeanObject,
    mut v_inv_5466_: *mut leanh::LeanObject,
    mut v_bs_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: *mut leanh::LeanObject,
    mut v___y_5469_: *mut leanh::LeanObject,
    mut v___y_5470_: *mut leanh::LeanObject,
    mut v___y_5471_: *mut leanh::LeanObject,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v___y_5473_: *mut leanh::LeanObject,
    mut v___y_5474_: *mut leanh::LeanObject,
    mut v___y_5475_: *mut leanh::LeanObject,
    mut v___y_5476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5477_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__4(v_as_5463_, v_i_5464_, v_j_5465_, v_inv_5466_, v_bs_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
    leanh::lean_dec(v___y_5475_);
    leanh::lean_dec_ref(v___y_5474_);
    leanh::lean_dec(v___y_5473_);
    leanh::lean_dec_ref(v___y_5472_);
    leanh::lean_dec(v___y_5471_);
    leanh::lean_dec_ref(v___y_5470_);
    leanh::lean_dec(v___y_5469_);
    leanh::lean_dec_ref(v___y_5468_);
    leanh::lean_dec_ref(v_as_5463_);
    return v_res_5477_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(
    mut v_00_u03b1_5478_: *mut leanh::LeanObject,
    mut v_msg_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5485_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___redArg(v_msg_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_);
    return v___x_5485_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8___boxed(
    mut v_00_u03b1_5486_: *mut leanh::LeanObject,
    mut v_msg_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
    mut v___y_5489_: *mut leanh::LeanObject,
    mut v___y_5490_: *mut leanh::LeanObject,
    mut v___y_5491_: *mut leanh::LeanObject,
    mut v___y_5492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5493_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__8(v_00_u03b1_5486_, v_msg_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
    leanh::lean_dec(v___y_5491_);
    leanh::lean_dec_ref(v___y_5490_);
    leanh::lean_dec(v___y_5489_);
    leanh::lean_dec_ref(v___y_5488_);
    return v_res_5493_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10(
    mut v_00_u03b2_5494_: *mut leanh::LeanObject,
    mut v_x_5495_: *mut leanh::LeanObject,
    mut v_x_5496_: *mut leanh::LeanObject,
    mut v_x_5497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5498_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10___redArg(v_x_5495_, v_x_5496_, v_x_5497_);
    return v___x_5498_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(
    mut v_00_u03b2_5499_: *mut leanh::LeanObject,
    mut v_x_5500_: *mut leanh::LeanObject,
    mut v_x_5501_: usize,
    mut v_x_5502_: usize,
    mut v_x_5503_: *mut leanh::LeanObject,
    mut v_x_5504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___redArg(v_x_5500_, v_x_5501_, v_x_5502_, v_x_5503_, v_x_5504_);
    return v___x_5505_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14___boxed(
    mut v_00_u03b2_5506_: *mut leanh::LeanObject,
    mut v_x_5507_: *mut leanh::LeanObject,
    mut v_x_5508_: *mut leanh::LeanObject,
    mut v_x_5509_: *mut leanh::LeanObject,
    mut v_x_5510_: *mut leanh::LeanObject,
    mut v_x_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_22757__boxed_5512_: usize = 0;
    let mut v_x_22758__boxed_5513_: usize = 0;
    let mut v_res_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_22757__boxed_5512_ = leanh::lean_unbox_usize(v_x_5508_);
    leanh::lean_dec(v_x_5508_);
    v_x_22758__boxed_5513_ = leanh::lean_unbox_usize(v_x_5509_);
    leanh::lean_dec(v_x_5509_);
    v_res_5514_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14(v_00_u03b2_5506_, v_x_5507_, v_x_22757__boxed_5512_, v_x_22758__boxed_5513_, v_x_5510_, v_x_5511_);
    return v_res_5514_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20(
    mut v_00_u03b2_5515_: *mut leanh::LeanObject,
    mut v_n_5516_: *mut leanh::LeanObject,
    mut v_k_5517_: *mut leanh::LeanObject,
    mut v_v_5518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5519_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20___redArg(v_n_5516_, v_k_5517_, v_v_5518_);
    return v___x_5519_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(
    mut v_00_u03b2_5520_: *mut leanh::LeanObject,
    mut v_depth_5521_: usize,
    mut v_keys_5522_: *mut leanh::LeanObject,
    mut v_vals_5523_: *mut leanh::LeanObject,
    mut v_heq_5524_: *mut leanh::LeanObject,
    mut v_i_5525_: *mut leanh::LeanObject,
    mut v_entries_5526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5527_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___redArg(v_depth_5521_, v_keys_5522_, v_vals_5523_, v_i_5525_, v_entries_5526_);
    return v___x_5527_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21___boxed(
    mut v_00_u03b2_5528_: *mut leanh::LeanObject,
    mut v_depth_5529_: *mut leanh::LeanObject,
    mut v_keys_5530_: *mut leanh::LeanObject,
    mut v_vals_5531_: *mut leanh::LeanObject,
    mut v_heq_5532_: *mut leanh::LeanObject,
    mut v_i_5533_: *mut leanh::LeanObject,
    mut v_entries_5534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5535_ = leanh::lean_unbox_usize(v_depth_5529_);
    leanh::lean_dec(v_depth_5529_);
    v_res_5536_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__21(v_00_u03b2_5528_, v_depth_boxed_5535_, v_keys_5530_, v_vals_5531_, v_heq_5532_, v_i_5533_, v_entries_5534_);
    leanh::lean_dec_ref(v_vals_5531_);
    leanh::lean_dec_ref(v_keys_5530_);
    return v_res_5536_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(
    mut v_00_u03b1_5537_: *mut leanh::LeanObject,
    mut v_name_5538_: *mut leanh::LeanObject,
    mut v_bi_5539_: u8,
    mut v_type_5540_: *mut leanh::LeanObject,
    mut v_k_5541_: *mut leanh::LeanObject,
    mut v_kind_5542_: u8,
    mut v___y_5543_: *mut leanh::LeanObject,
    mut v___y_5544_: *mut leanh::LeanObject,
    mut v___y_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5552_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___redArg(v_name_5538_, v_bi_5539_, v_type_5540_, v_k_5541_, v_kind_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
    return v___x_5552_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21___boxed(
    mut v_00_u03b1_5553_: *mut leanh::LeanObject,
    mut v_name_5554_: *mut leanh::LeanObject,
    mut v_bi_5555_: *mut leanh::LeanObject,
    mut v_type_5556_: *mut leanh::LeanObject,
    mut v_k_5557_: *mut leanh::LeanObject,
    mut v_kind_5558_: *mut leanh::LeanObject,
    mut v___y_5559_: *mut leanh::LeanObject,
    mut v___y_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
    mut v___y_5567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_5568_: u8 = 0;
    let mut v_kind_boxed_5569_: u8 = 0;
    let mut v_res_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5568_ = (leanh::lean_unbox(v_bi_5555_) as u8);
    v_kind_boxed_5569_ = (leanh::lean_unbox(v_kind_5558_) as u8);
    v_res_5570_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_Elab_Tactic_Do_ProofMode_mRevertForallN___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__1_spec__5_spec__8_spec__14_spec__19_spec__21(v_00_u03b1_5553_, v_name_5554_, v_bi_boxed_5568_, v_type_5556_, v_k_5557_, v_kind_boxed_5569_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
    leanh::lean_dec(v___y_5566_);
    leanh::lean_dec_ref(v___y_5565_);
    leanh::lean_dec(v___y_5564_);
    leanh::lean_dec_ref(v___y_5563_);
    leanh::lean_dec(v___y_5562_);
    leanh::lean_dec_ref(v___y_5561_);
    leanh::lean_dec(v___y_5560_);
    leanh::lean_dec_ref(v___y_5559_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22(
    mut v_00_u03b2_5571_: *mut leanh::LeanObject,
    mut v_x_5572_: *mut leanh::LeanObject,
    mut v_x_5573_: *mut leanh::LeanObject,
    mut v_x_5574_: *mut leanh::LeanObject,
    mut v_x_5575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5576_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRevert_spec__2_spec__10_spec__14_spec__20_spec__22___redArg(v_x_5572_, v_x_5573_, v_x_5574_, v_x_5575_);
    return v___x_5576_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1()
-> *mut leanh::LeanObject {
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5588_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5589_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___closed__3;
    v___x_5590_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___closed__3;
    v___x_5591_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMRevert___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5592_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5588_,
        v___x_5589_,
        v___x_5590_,
        v___x_5591_,
    );
    return v___x_5592_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1___boxed(
    mut v_a_5593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5594_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
    return v_res_5594_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Revert_0__Lean_Elab_Tactic_Do_ProofMode_elabMRevert___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRevert__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Revert(builtin);
}