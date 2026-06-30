// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Intro
// Imports: Lean.Elab.Tactic.Do.ProofMode.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_expr_instantiate1, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Control::Basic::l_instMonadControlTOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_TSyntax_getId, l_Lean_mkFreshId___redArg, l_Lean_monadNameGeneratorLift___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Array_mkArray1___redArg, l_Lean_Macro_throwUnsupported___redArg,
    l_Lean_Name_mkStr6, l_Lean_Name_num___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getNumArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_addMacroScope,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed, l_ReaderT_pure___boxed, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadNameGeneratorCoreM, l_Lean_Core_instMonadQuotationCoreM,
    l_Lean_Core_mkFreshUserName, l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
    l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd, l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed,
    l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName,
    l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwError___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_betaRev,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp5, l_Lean_mkApp7, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instAddMessageContextMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLambdaFVars___boxed, l_Lean_Meta_mkLetFVars, l_Lean_Meta_mkLetFVars___boxed,
    l_Lean_Meta_withLetDecl___redArg, l_Lean_Meta_withLocalDeclD___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value:
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
    m_data: [73, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value:
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
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__23_value)
            as *mut leanh::LeanObject,
        9462318056131769598 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value:
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
    m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__26_value)
            as *mut leanh::LeanObject,
        13771926289831477797 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__28_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_value:
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
        84, 97, 114, 103, 101, 116, 32, 110, 111, 116, 32, 97, 110, 32, 105, 109, 112, 108, 105,
        99, 97, 116, 105, 111, 110, 32, 111, 114, 32, 108, 101, 116, 45, 98, 105, 110, 100, 105,
        110, 103, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value:
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
        101, 110, 116, 97, 105, 108, 115, 95, 99, 111, 110, 115, 95, 105, 110, 116, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        16895493190937329785 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value:
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
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value:
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
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__1_value
        ) as *mut leanh::LeanObject,
        8614124190858717794 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        65, 109, 98, 105, 101, 110, 116, 32, 115, 116, 97, 116, 101, 32, 108, 105, 115, 116, 32,
        110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        5370976759840893899 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value:
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
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_1:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_2:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        3984140175429830279 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 105, 110, 116, 114, 111, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value) as *mut leanh::LeanObject,14630191664228916872 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 105, 110, 116, 114, 111, 80, 97, 116, 95, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value) as *mut leanh::LeanObject,11933896700979561751 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 99, 97, 115, 101, 115, 80, 97, 116, 95, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value) as *mut leanh::LeanObject,9115185665287701673 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 101, 113, 49, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value) as *mut leanh::LeanObject,8471002125274025202 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__8_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 99, 97, 115, 101, 115, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14_value) as *mut leanh::LeanObject,1713051840268779758 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,18104247681175793831 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1_value) as *mut leanh::LeanObject,6741459752716500089 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2_value) as *mut leanh::LeanObject,11795487225838515618 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 11,
    m_data: [
        109, 105, 110, 116, 114, 111, 80, 97, 116, 226, 136, 128, 95, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__0_value)
            as *mut leanh::LeanObject,
        4029293156818995509 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 73, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__25_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__1_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__2_value) as *mut leanh::LeanObject,3890238722989323077 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__0(
    mut v_val_2245_: *mut leanh::LeanObject,
    mut v_inst_2246_: *mut leanh::LeanObject,
    mut v_prf_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2248_ = leanh::lean_unsigned_to_nat(1);
    v___x_2249_ = lean_mk_empty_array_with_capacity(v___x_2248_);
    v___x_2250_ = lean_array_push(v___x_2249_, v_val_2245_);
    v___x_2251_ = 1;
    v___x_2252_ = 1;
    v___x_2253_ = leanh::lean_box((v___x_2251_) as usize);
    v___x_2254_ = leanh::lean_box((v___x_2251_) as usize);
    v___x_2255_ = leanh::lean_box((v___x_2252_) as usize);
    v___x_2256_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLetFVars___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    leanh::lean_closure_set(v___x_2256_, 0, v___x_2250_);
    leanh::lean_closure_set(v___x_2256_, 1, v_prf_2247_);
    leanh::lean_closure_set(v___x_2256_, 2, v___x_2253_);
    leanh::lean_closure_set(v___x_2256_, 3, v___x_2254_);
    leanh::lean_closure_set(v___x_2256_, 4, v___x_2255_);
    v___x_2257_ = leanh::lean_apply_2(v_inst_2246_, leanh::lean_box(0), v___x_2256_);
    return v___x_2257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1(
    mut v_inst_2258_: *mut leanh::LeanObject,
    mut v_body_2259_: *mut leanh::LeanObject,
    mut v_u_2260_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2261_: *mut leanh::LeanObject,
    mut v_hyps_2262_: *mut leanh::LeanObject,
    mut v_k_2263_: *mut leanh::LeanObject,
    mut v_toBind_2264_: *mut leanh::LeanObject,
    mut v_val_2265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_val_2265_);
    v___f_2266_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2266_, 0, v_val_2265_);
    leanh::lean_closure_set(v___f_2266_, 1, v_inst_2258_);
    v___x_2267_ = lean_expr_instantiate1(v_body_2259_, v_val_2265_);
    leanh::lean_dec_ref(v_val_2265_);
    v___x_2268_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2268_, 0, v_u_2260_);
    leanh::lean_ctor_set(v___x_2268_, 1, v_00_u03c3s_2261_);
    leanh::lean_ctor_set(v___x_2268_, 2, v_hyps_2262_);
    leanh::lean_ctor_set(v___x_2268_, 3, v___x_2267_);
    v___x_2269_ = leanh::lean_apply_1(v_k_2263_, v___x_2268_);
    v___x_2270_ = leanh::lean_apply_4(
        v_toBind_2264_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2269_,
        v___f_2266_,
    );
    return v___x_2270_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed(
    mut v_inst_2271_: *mut leanh::LeanObject,
    mut v_body_2272_: *mut leanh::LeanObject,
    mut v_u_2273_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2274_: *mut leanh::LeanObject,
    mut v_hyps_2275_: *mut leanh::LeanObject,
    mut v_k_2276_: *mut leanh::LeanObject,
    mut v_toBind_2277_: *mut leanh::LeanObject,
    mut v_val_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2279_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1(
        v_inst_2271_,
        v_body_2272_,
        v_u_2273_,
        v_00_u03c3s_2274_,
        v_hyps_2275_,
        v_k_2276_,
        v_toBind_2277_,
        v_val_2278_,
    );
    leanh::lean_dec_ref(v_body_2272_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(
    mut v_inst_2280_: *mut leanh::LeanObject,
    mut v_inst_2281_: *mut leanh::LeanObject,
    mut v_type_2282_: *mut leanh::LeanObject,
    mut v_value_2283_: *mut leanh::LeanObject,
    mut v___f_2284_: *mut leanh::LeanObject,
    mut v___x_2285_: u8,
    mut v_name_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2287_ = 0;
    v___x_2288_ = l_Lean_Meta_withLetDecl___redArg(
        v_inst_2280_,
        v_inst_2281_,
        v_name_2286_,
        v_type_2282_,
        v_value_2283_,
        v___f_2284_,
        v___x_2285_,
        v___x_2287_,
    );
    return v___x_2288_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed(
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_inst_2290_: *mut leanh::LeanObject,
    mut v_type_2291_: *mut leanh::LeanObject,
    mut v_value_2292_: *mut leanh::LeanObject,
    mut v___f_2293_: *mut leanh::LeanObject,
    mut v___x_2294_: *mut leanh::LeanObject,
    mut v_name_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1357__boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357__boxed_2296_ = (leanh::lean_unbox(v___x_2294_) as u8);
    v_res_2297_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2(
        v_inst_2289_,
        v_inst_2290_,
        v_type_2291_,
        v_value_2292_,
        v___f_2293_,
        v___x_1357__boxed_2296_,
        v_name_2295_,
    );
    return v_res_2297_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3(
    mut v___f_2298_: *mut leanh::LeanObject,
    mut v_name_2299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = leanh::lean_apply_1(v___f_2298_, v_name_2299_);
    return v___x_2300_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(
    mut v_declName_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2307_ = l_Lean_Core_mkFreshUserName(v_declName_2301_, v___y_2304_, v___y_2305_);
    return v___x_2307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed(
    mut v_declName_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4(
        v_declName_2308_,
        v___y_2309_,
        v___y_2310_,
        v___y_2311_,
        v___y_2312_,
    );
    leanh::lean_dec(v___y_2312_);
    leanh::lean_dec_ref(v___y_2311_);
    leanh::lean_dec(v___y_2310_);
    leanh::lean_dec_ref(v___y_2309_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(
    mut v_ident_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
    mut v___y_2317_: *mut leanh::LeanObject,
    mut v___y_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ =
        l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_ident_2315_, v___y_2318_, v___y_2319_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed(
    mut v_ident_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
    mut v___y_2324_: *mut leanh::LeanObject,
    mut v___y_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
    mut v___y_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8(
        v_ident_2322_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
        v___y_2326_,
    );
    leanh::lean_dec(v___y_2326_);
    leanh::lean_dec_ref(v___y_2325_);
    leanh::lean_dec(v___y_2324_);
    leanh::lean_dec_ref(v___y_2323_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5(
    mut v___x_2332_: *mut leanh::LeanObject,
    mut v___x_2333_: *mut leanh::LeanObject,
    mut v___x_2334_: *mut leanh::LeanObject,
    mut v_u_2335_: *mut leanh::LeanObject,
    mut v___x_2336_: *mut leanh::LeanObject,
    mut v_fst_2337_: *mut leanh::LeanObject,
    mut v_hyps_2338_: *mut leanh::LeanObject,
    mut v_H_2339_: *mut leanh::LeanObject,
    mut v___x_2340_: *mut leanh::LeanObject,
    mut v_snd_2341_: *mut leanh::LeanObject,
    mut v_toPure_2342_: *mut leanh::LeanObject,
    mut v_prf_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__0;
    v___x_2345_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__1;
    v___x_2346_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5___closed__2;
    v___x_2347_ = l_Lean_Name_mkStr6(
        v___x_2332_,
        v___x_2333_,
        v___x_2334_,
        v___x_2344_,
        v___x_2345_,
        v___x_2346_,
    );
    v___x_2348_ = leanh::lean_box(0);
    v___x_2349_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2349_, 0, v_u_2335_);
    leanh::lean_ctor_set(v___x_2349_, 1, v___x_2348_);
    v___x_2350_ = l_Lean_mkConst(v___x_2347_, v___x_2349_);
    v_prf_2351_ = l_Lean_mkApp7(
        v___x_2350_,
        v___x_2336_,
        v_fst_2337_,
        v_hyps_2338_,
        v_H_2339_,
        v___x_2340_,
        v_snd_2341_,
        v_prf_2343_,
    );
    v___x_2352_ =
        leanh::lean_apply_2(v_toPure_2342_, leanh::lean_box(0), v_prf_2351_);
    return v___x_2352_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6(
    mut v_hyp_2353_: *mut leanh::LeanObject,
    mut v_u_2354_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2355_: *mut leanh::LeanObject,
    mut v_hyps_2356_: *mut leanh::LeanObject,
    mut v___x_2357_: *mut leanh::LeanObject,
    mut v___x_2358_: *mut leanh::LeanObject,
    mut v___x_2359_: *mut leanh::LeanObject,
    mut v___x_2360_: *mut leanh::LeanObject,
    mut v___x_2361_: *mut leanh::LeanObject,
    mut v_toPure_2362_: *mut leanh::LeanObject,
    mut v_k_2363_: *mut leanh::LeanObject,
    mut v_toBind_2364_: *mut leanh::LeanObject,
    mut v_____r_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_H_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_H_2366_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_2353_);
    leanh::lean_inc_ref(v_H_2366_);
    leanh::lean_inc_ref(v_hyps_2356_);
    leanh::lean_inc_ref(v_00_u03c3s_2355_);
    leanh::lean_inc_n(v_u_2354_, 2);
    v___x_2367_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
        v_u_2354_,
        v_00_u03c3s_2355_,
        v_hyps_2356_,
        v_H_2366_,
    );
    v_fst_2368_ = leanh::lean_ctor_get(v___x_2367_, 0);
    leanh::lean_inc_n(v_fst_2368_, 2);
    v_snd_2369_ = leanh::lean_ctor_get(v___x_2367_, 1);
    leanh::lean_inc(v_snd_2369_);
    leanh::lean_dec_ref(v___x_2367_);
    leanh::lean_inc_ref(v___x_2361_);
    v___f_2370_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__5 as *mut core::ffi::c_void,
        12,
        11,
    );
    leanh::lean_closure_set(v___f_2370_, 0, v___x_2357_);
    leanh::lean_closure_set(v___f_2370_, 1, v___x_2358_);
    leanh::lean_closure_set(v___f_2370_, 2, v___x_2359_);
    leanh::lean_closure_set(v___f_2370_, 3, v_u_2354_);
    leanh::lean_closure_set(v___f_2370_, 4, v___x_2360_);
    leanh::lean_closure_set(v___f_2370_, 5, v_fst_2368_);
    leanh::lean_closure_set(v___f_2370_, 6, v_hyps_2356_);
    leanh::lean_closure_set(v___f_2370_, 7, v_H_2366_);
    leanh::lean_closure_set(v___f_2370_, 8, v___x_2361_);
    leanh::lean_closure_set(v___f_2370_, 9, v_snd_2369_);
    leanh::lean_closure_set(v___f_2370_, 10, v_toPure_2362_);
    v___x_2371_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2371_, 0, v_u_2354_);
    leanh::lean_ctor_set(v___x_2371_, 1, v_00_u03c3s_2355_);
    leanh::lean_ctor_set(v___x_2371_, 2, v_fst_2368_);
    leanh::lean_ctor_set(v___x_2371_, 3, v___x_2361_);
    v___x_2372_ = leanh::lean_apply_1(v_k_2363_, v___x_2371_);
    v___x_2373_ = leanh::lean_apply_4(
        v_toBind_2364_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2372_,
        v___f_2370_,
    );
    return v___x_2373_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(
    mut v_fst_2374_: *mut leanh::LeanObject,
    mut v___x_2375_: *mut leanh::LeanObject,
    mut v_u_2376_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2377_: *mut leanh::LeanObject,
    mut v_hyps_2378_: *mut leanh::LeanObject,
    mut v___x_2379_: *mut leanh::LeanObject,
    mut v___x_2380_: *mut leanh::LeanObject,
    mut v___x_2381_: *mut leanh::LeanObject,
    mut v___x_2382_: *mut leanh::LeanObject,
    mut v___x_2383_: *mut leanh::LeanObject,
    mut v_toPure_2384_: *mut leanh::LeanObject,
    mut v_k_2385_: *mut leanh::LeanObject,
    mut v_toBind_2386_: *mut leanh::LeanObject,
    mut v_snd_2387_: *mut leanh::LeanObject,
    mut v___x_2388_: u8,
    mut v_inst_2389_: *mut leanh::LeanObject,
    mut v_uniq_2390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hyp_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hyp_2391_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v_hyp_2391_, 0, v_fst_2374_);
    leanh::lean_ctor_set(v_hyp_2391_, 1, v_uniq_2390_);
    leanh::lean_ctor_set(v_hyp_2391_, 2, v___x_2375_);
    leanh::lean_inc(v_toBind_2386_);
    leanh::lean_inc_ref(v___x_2382_);
    leanh::lean_inc_ref(v_hyp_2391_);
    v___f_2392_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__6 as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_2392_, 0, v_hyp_2391_);
    leanh::lean_closure_set(v___f_2392_, 1, v_u_2376_);
    leanh::lean_closure_set(v___f_2392_, 2, v_00_u03c3s_2377_);
    leanh::lean_closure_set(v___f_2392_, 3, v_hyps_2378_);
    leanh::lean_closure_set(v___f_2392_, 4, v___x_2379_);
    leanh::lean_closure_set(v___f_2392_, 5, v___x_2380_);
    leanh::lean_closure_set(v___f_2392_, 6, v___x_2381_);
    leanh::lean_closure_set(v___f_2392_, 7, v___x_2382_);
    leanh::lean_closure_set(v___f_2392_, 8, v___x_2383_);
    leanh::lean_closure_set(v___f_2392_, 9, v_toPure_2384_);
    leanh::lean_closure_set(v___f_2392_, 10, v_k_2385_);
    leanh::lean_closure_set(v___f_2392_, 11, v_toBind_2386_);
    v___x_2393_ = leanh::lean_box((v___x_2388_) as usize);
    v___x_2394_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_2394_, 0, v_snd_2387_);
    leanh::lean_closure_set(v___x_2394_, 1, v___x_2382_);
    leanh::lean_closure_set(v___x_2394_, 2, v_hyp_2391_);
    leanh::lean_closure_set(v___x_2394_, 3, v___x_2393_);
    v___x_2395_ = leanh::lean_apply_2(v_inst_2389_, leanh::lean_box(0), v___x_2394_);
    v___x_2396_ = leanh::lean_apply_4(
        v_toBind_2386_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2395_,
        v___f_2392_,
    );
    return v___x_2396_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2397_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_2398_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_u_2399_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3s_2400_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_hyps_2401_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2402_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2403_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2404_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2405_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2406_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_toPure_2407_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_k_2408_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_toBind_2409_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_snd_2410_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2411_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_inst_2412_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_uniq_2413_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_1488__boxed_2414_: u8 = 0;
    let mut v_res_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1488__boxed_2414_ = (leanh::lean_unbox(v___x_2411_) as u8);
    v_res_2415_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7(
        v_fst_2397_,
        v___x_2398_,
        v_u_2399_,
        v_00_u03c3s_2400_,
        v_hyps_2401_,
        v___x_2402_,
        v___x_2403_,
        v___x_2404_,
        v___x_2405_,
        v___x_2406_,
        v_toPure_2407_,
        v_k_2408_,
        v_toBind_2409_,
        v_snd_2410_,
        v___x_1488__boxed_2414_,
        v_inst_2412_,
        v_uniq_2413_,
    );
    return v_res_2415_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(
    mut v___x_2416_: *mut leanh::LeanObject,
    mut v_u_2417_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2418_: *mut leanh::LeanObject,
    mut v_hyps_2419_: *mut leanh::LeanObject,
    mut v___x_2420_: *mut leanh::LeanObject,
    mut v___x_2421_: *mut leanh::LeanObject,
    mut v___x_2422_: *mut leanh::LeanObject,
    mut v___x_2423_: *mut leanh::LeanObject,
    mut v___x_2424_: *mut leanh::LeanObject,
    mut v_toPure_2425_: *mut leanh::LeanObject,
    mut v_k_2426_: *mut leanh::LeanObject,
    mut v_toBind_2427_: *mut leanh::LeanObject,
    mut v___x_2428_: u8,
    mut v_inst_2429_: *mut leanh::LeanObject,
    mut v___x_2430_: *mut leanh::LeanObject,
    mut v___x_2431_: *mut leanh::LeanObject,
    mut v_____x_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2433_ = leanh::lean_ctor_get(v_____x_2432_, 0);
    leanh::lean_inc(v_fst_2433_);
    v_snd_2434_ = leanh::lean_ctor_get(v_____x_2432_, 1);
    leanh::lean_inc(v_snd_2434_);
    leanh::lean_dec_ref(v_____x_2432_);
    v___x_2435_ = leanh::lean_box((v___x_2428_) as usize);
    leanh::lean_inc(v_inst_2429_);
    leanh::lean_inc(v_toBind_2427_);
    v___f_2436_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__7___boxed as *mut core::ffi::c_void,
        17,
        16,
    );
    leanh::lean_closure_set(v___f_2436_, 0, v_fst_2433_);
    leanh::lean_closure_set(v___f_2436_, 1, v___x_2416_);
    leanh::lean_closure_set(v___f_2436_, 2, v_u_2417_);
    leanh::lean_closure_set(v___f_2436_, 3, v_00_u03c3s_2418_);
    leanh::lean_closure_set(v___f_2436_, 4, v_hyps_2419_);
    leanh::lean_closure_set(v___f_2436_, 5, v___x_2420_);
    leanh::lean_closure_set(v___f_2436_, 6, v___x_2421_);
    leanh::lean_closure_set(v___f_2436_, 7, v___x_2422_);
    leanh::lean_closure_set(v___f_2436_, 8, v___x_2423_);
    leanh::lean_closure_set(v___f_2436_, 9, v___x_2424_);
    leanh::lean_closure_set(v___f_2436_, 10, v_toPure_2425_);
    leanh::lean_closure_set(v___f_2436_, 11, v_k_2426_);
    leanh::lean_closure_set(v___f_2436_, 12, v_toBind_2427_);
    leanh::lean_closure_set(v___f_2436_, 13, v_snd_2434_);
    leanh::lean_closure_set(v___f_2436_, 14, v___x_2435_);
    leanh::lean_closure_set(v___f_2436_, 15, v_inst_2429_);
    v___x_2437_ = l_Lean_mkFreshId___redArg(v___x_2430_, v___x_2431_);
    v___x_2438_ = leanh::lean_apply_2(v_inst_2429_, leanh::lean_box(0), v___x_2437_);
    v___x_2439_ = leanh::lean_apply_4(
        v_toBind_2427_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2438_,
        v___f_2436_,
    );
    return v___x_2439_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2440_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_u_2441_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3s_2442_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_hyps_2443_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2444_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2445_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2446_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2447_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2448_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_toPure_2449_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_k_2450_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_toBind_2451_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_2452_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_inst_2453_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2454_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___x_2455_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_____x_2456_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_1526__boxed_2457_: u8 = 0;
    let mut v_res_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1526__boxed_2457_ = (leanh::lean_unbox(v___x_2452_) as u8);
    v_res_2458_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9(
        v___x_2440_,
        v_u_2441_,
        v_00_u03c3s_2442_,
        v_hyps_2443_,
        v___x_2444_,
        v___x_2445_,
        v___x_2446_,
        v___x_2447_,
        v___x_2448_,
        v_toPure_2449_,
        v_k_2450_,
        v_toBind_2451_,
        v___x_1526__boxed_2457_,
        v_inst_2453_,
        v___x_2454_,
        v___x_2455_,
        v_____x_2456_,
    );
    return v_res_2458_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2459_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2459_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__0,
    );
    v___x_2461_ = l_StateRefT_x27_instMonad___redArg(v___x_2460_);
    return v___x_2461_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_Core_instMonadNameGeneratorCoreM;
    v___x_2469_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5;
    v___x_2470_ = l_Lean_monadNameGeneratorLift___redArg(v___x_2469_, v___x_2468_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2471_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__8,
    );
    v___f_2472_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4;
    v___x_2473_ = l_Lean_monadNameGeneratorLift___redArg(v___f_2472_, v___x_2471_);
    return v___x_2473_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_2475_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2475_, 0, v___x_2474_);
    return v___f_2475_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_2477_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2477_, 0, v___x_2476_);
    return v___f_2477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___f_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2478_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__11,
    );
    v___f_2479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__10,
    );
    v___x_2480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2480_, 0, v___f_2479_);
    leanh::lean_ctor_set(v___x_2480_, 1, v___f_2478_);
    return v___x_2480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12,
    );
    v___f_2482_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2482_, 0, v___x_2481_);
    return v___f_2482_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__12,
    );
    v___f_2484_ = leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2484_, 0, v___x_2483_);
    return v___f_2484_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___f_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__14,
    );
    v___f_2486_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__13,
    );
    v___x_2487_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2487_, 0, v___f_2486_);
    leanh::lean_ctor_set(v___x_2487_, 1, v___f_2485_);
    return v___x_2487_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_2491_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__5;
    v___x_2492_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__17;
    v___x_2493_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_2492_,
        v___x_2491_,
        v___x_2490_,
    );
    return v___x_2493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__18,
    );
    v___f_2495_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__4;
    v___f_2496_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__16;
    v___x_2497_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_2496_,
        v___f_2495_,
        v___x_2494_,
    );
    return v___x_2497_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__30;
    v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
    return v___x_2517_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(
    mut v_inst_2518_: *mut leanh::LeanObject,
    mut v_inst_2519_: *mut leanh::LeanObject,
    mut v_inst_2520_: *mut leanh::LeanObject,
    mut v_goal_2521_: *mut leanh::LeanObject,
    mut v_ident_2522_: *mut leanh::LeanObject,
    mut v_k_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2544_: u8 = 0;
    let mut v_toFunctor_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v___f_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v_declName_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___f_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: u8 = 0;
    let mut v___f_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2619_: u8 = 0;
    let mut v_unused_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_unused_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut v_unused_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2524_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1,
                );
                v_toApplicative_2525_ = leanh::lean_ctor_get(v___x_2524_, 0);
                v_toFunctor_2526_ = leanh::lean_ctor_get(v_toApplicative_2525_, 0);
                v_toSeq_2527_ = leanh::lean_ctor_get(v_toApplicative_2525_, 2);
                v_toSeqLeft_2528_ = leanh::lean_ctor_get(v_toApplicative_2525_, 3);
                v_toSeqRight_2529_ = leanh::lean_ctor_get(v_toApplicative_2525_, 4);
                v___f_2530_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2;
                v___f_2531_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2526_, 2);
                v___f_2532_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2532_, 0, v_toFunctor_2526_);
                v___f_2533_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2533_, 0, v_toFunctor_2526_);
                v___x_2534_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2534_, 0, v___f_2532_);
                leanh::lean_ctor_set(v___x_2534_, 1, v___f_2533_);
                leanh::lean_inc(v_toSeqRight_2529_);
                v___f_2535_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2535_, 0, v_toSeqRight_2529_);
                leanh::lean_inc(v_toSeqLeft_2528_);
                v___f_2536_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2536_, 0, v_toSeqLeft_2528_);
                leanh::lean_inc(v_toSeq_2527_);
                v___f_2537_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2537_, 0, v_toSeq_2527_);
                v___x_2538_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2538_, 0, v___x_2534_);
                leanh::lean_ctor_set(v___x_2538_, 1, v___f_2530_);
                leanh::lean_ctor_set(v___x_2538_, 2, v___f_2537_);
                leanh::lean_ctor_set(v___x_2538_, 3, v___f_2536_);
                leanh::lean_ctor_set(v___x_2538_, 4, v___f_2535_);
                v___x_2539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2539_, 0, v___x_2538_);
                leanh::lean_ctor_set(v___x_2539_, 1, v___f_2531_);
                v___x_2540_ = l_StateRefT_x27_instMonad___redArg(v___x_2539_);
                v_toApplicative_2541_ = leanh::lean_ctor_get(v___x_2540_, 0);
                v_isSharedCheck_2636_ = (!leanh::lean_is_exclusive(v___x_2540_)) as u8;
                if v_isSharedCheck_2636_ == 0 {
                    v_unused_2637_ = leanh::lean_ctor_get(v___x_2540_, 1);
                    leanh::lean_dec(v_unused_2637_);
                    v___x_2543_ = v___x_2540_;
                    v_isShared_2544_ = v_isSharedCheck_2636_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2541_);
                    leanh::lean_dec(v___x_2540_);
                    v___x_2543_ = leanh::lean_box(0);
                    v_isShared_2544_ = v_isSharedCheck_2636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2545_ = leanh::lean_ctor_get(v_toApplicative_2541_, 0);
                v_toSeq_2546_ = leanh::lean_ctor_get(v_toApplicative_2541_, 2);
                v_toSeqLeft_2547_ = leanh::lean_ctor_get(v_toApplicative_2541_, 3);
                v_toSeqRight_2548_ = leanh::lean_ctor_get(v_toApplicative_2541_, 4);
                v_isSharedCheck_2634_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2541_)) as u8;
                if v_isSharedCheck_2634_ == 0 {
                    v_unused_2635_ = leanh::lean_ctor_get(v_toApplicative_2541_, 1);
                    leanh::lean_dec(v_unused_2635_);
                    v___x_2550_ = v_toApplicative_2541_;
                    v_isShared_2551_ = v_isSharedCheck_2634_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2548_);
                    leanh::lean_inc(v_toSeqLeft_2547_);
                    leanh::lean_inc(v_toSeq_2546_);
                    leanh::lean_inc(v_toFunctor_2545_);
                    leanh::lean_dec(v_toApplicative_2541_);
                    v___x_2550_ = leanh::lean_box(0);
                    v_isShared_2551_ = v_isSharedCheck_2634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2552_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6;
                v___f_2553_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7;
                leanh::lean_inc_ref(v_toFunctor_2545_);
                v___f_2554_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2554_, 0, v_toFunctor_2545_);
                v___f_2555_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2555_, 0, v_toFunctor_2545_);
                v___x_2556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2556_, 0, v___f_2554_);
                leanh::lean_ctor_set(v___x_2556_, 1, v___f_2555_);
                v___f_2557_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2557_, 0, v_toSeqRight_2548_);
                v___f_2558_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2558_, 0, v_toSeqLeft_2547_);
                v___f_2559_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2559_, 0, v_toSeq_2546_);
                if v_isShared_2551_ == 0 {
                    leanh::lean_ctor_set(v___x_2550_, 4, v___f_2557_);
                    leanh::lean_ctor_set(v___x_2550_, 3, v___f_2558_);
                    leanh::lean_ctor_set(v___x_2550_, 2, v___f_2559_);
                    leanh::lean_ctor_set(v___x_2550_, 1, v___f_2552_);
                    leanh::lean_ctor_set(v___x_2550_, 0, v___x_2556_);
                    v___x_2561_ = v___x_2550_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___f_2552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 2, v___f_2559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 3, v___f_2558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 4, v___f_2557_);
                    v___x_2561_ = v_reuseFailAlloc_2633_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2544_ == 0 {
                    leanh::lean_ctor_set(v___x_2543_, 1, v___f_2553_);
                    leanh::lean_ctor_set(v___x_2543_, 0, v___x_2561_);
                    v___x_2563_ = v___x_2543_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 1, v___f_2553_);
                    v___x_2563_ = v_reuseFailAlloc_2632_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2564_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__9,
                );
                v___x_2565_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15,
                );
                v___x_2566_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19,
                );
                v_toMonadRef_2567_ = leanh::lean_ctor_get(v___x_2566_, 0);
                v___x_2568_ = l_Lean_Meta_instAddMessageContextMetaM;
                leanh::lean_inc_ref(v___x_2563_);
                v___x_2569_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_2568_,
                    v___x_2563_,
                );
                leanh::lean_inc_ref(v_toMonadRef_2567_);
                v___x_2570_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2570_, 0, v___x_2565_);
                leanh::lean_ctor_set(v___x_2570_, 1, v_toMonadRef_2567_);
                leanh::lean_ctor_set(v___x_2570_, 2, v___x_2569_);
                v_toApplicative_2571_ = leanh::lean_ctor_get(v_inst_2518_, 0);
                v_toBind_2572_ = leanh::lean_ctor_get(v_inst_2518_, 1);
                v_toPure_2573_ = leanh::lean_ctor_get(v_toApplicative_2571_, 1);
                v_u_2574_ = leanh::lean_ctor_get(v_goal_2521_, 0);
                leanh::lean_inc(v_u_2574_);
                v_00_u03c3s_2575_ = leanh::lean_ctor_get(v_goal_2521_, 1);
                leanh::lean_inc_ref(v_00_u03c3s_2575_);
                v_hyps_2576_ = leanh::lean_ctor_get(v_goal_2521_, 2);
                leanh::lean_inc_ref(v_hyps_2576_);
                v_target_2577_ = leanh::lean_ctor_get(v_goal_2521_, 3);
                leanh::lean_inc_ref(v_target_2577_);
                leanh::lean_dec_ref(v_goal_2521_);
                v___x_2578_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__20;
                v___x_2579_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__21;
                v___x_2580_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__22;
                v___x_2581_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24;
                v___x_2582_ = leanh::lean_unsigned_to_nat(3);
                v___x_2583_ = l_Lean_Expr_isAppOfArity(v_target_2577_, v___x_2581_, v___x_2582_);
                if v___x_2583_ == 0 {
                    if leanh::lean_obj_tag(v_target_2577_) == 8 {
                        leanh::lean_inc(v_toPure_2573_);
                        leanh::lean_inc_n(v_toBind_2572_, 2);
                        leanh::lean_dec_ref_known(v___x_2570_, 3);
                        leanh::lean_dec_ref(v___x_2563_);
                        v_declName_2584_ = leanh::lean_ctor_get(v_target_2577_, 0);
                        leanh::lean_inc(v_declName_2584_);
                        v_type_2585_ = leanh::lean_ctor_get(v_target_2577_, 1);
                        leanh::lean_inc_ref(v_type_2585_);
                        v_value_2586_ = leanh::lean_ctor_get(v_target_2577_, 2);
                        leanh::lean_inc_ref(v_value_2586_);
                        v_body_2587_ = leanh::lean_ctor_get(v_target_2577_, 3);
                        leanh::lean_inc_ref(v_body_2587_);
                        leanh::lean_dec_ref_known(v_target_2577_, 4);
                        leanh::lean_inc(v_inst_2520_);
                        v___f_2588_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__1___boxed
                                as *mut core::ffi::c_void,
                            8,
                            7,
                        );
                        leanh::lean_closure_set(v___f_2588_, 0, v_inst_2520_);
                        leanh::lean_closure_set(v___f_2588_, 1, v_body_2587_);
                        leanh::lean_closure_set(v___f_2588_, 2, v_u_2574_);
                        leanh::lean_closure_set(v___f_2588_, 3, v_00_u03c3s_2575_);
                        leanh::lean_closure_set(v___f_2588_, 4, v_hyps_2576_);
                        leanh::lean_closure_set(v___f_2588_, 5, v_k_2523_);
                        leanh::lean_closure_set(v___f_2588_, 6, v_toBind_2572_);
                        v___x_2589_ = leanh::lean_box((v___x_2583_) as usize);
                        v___f_2590_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        leanh::lean_closure_set(v___f_2590_, 0, v_inst_2519_);
                        leanh::lean_closure_set(v___f_2590_, 1, v_inst_2518_);
                        leanh::lean_closure_set(v___f_2590_, 2, v_type_2585_);
                        leanh::lean_closure_set(v___f_2590_, 3, v_value_2586_);
                        leanh::lean_closure_set(v___f_2590_, 4, v___f_2588_);
                        leanh::lean_closure_set(v___f_2590_, 5, v___x_2589_);
                        v___x_2591_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        leanh::lean_inc(v_ident_2522_);
                        v___x_2592_ = l_Lean_Syntax_isOfKind(v_ident_2522_, v___x_2591_);
                        if v___x_2592_ == 0 {
                            leanh::lean_dec(v_toPure_2573_);
                            leanh::lean_dec(v_ident_2522_);
                            v___f_2593_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            leanh::lean_closure_set(v___f_2593_, 0, v___f_2590_);
                            v___f_2594_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed
                                    as *mut core::ffi::c_void,
                                6,
                                1,
                            );
                            leanh::lean_closure_set(v___f_2594_, 0, v_declName_2584_);
                            v___x_2595_ = leanh::lean_apply_2(
                                v_inst_2520_,
                                leanh::lean_box(0),
                                v___f_2594_,
                            );
                            v___x_2596_ = leanh::lean_apply_4(
                                v_toBind_2572_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2595_,
                                v___f_2593_,
                            );
                            return v___x_2596_;
                        } else {
                            v___x_2597_ = leanh::lean_unsigned_to_nat(0);
                            v_name_2598_ = l_Lean_Syntax_getArg(v_ident_2522_, v___x_2597_);
                            leanh::lean_dec(v_ident_2522_);
                            v___x_2599_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29;
                            leanh::lean_inc(v_name_2598_);
                            v___x_2600_ = l_Lean_Syntax_isOfKind(v_name_2598_, v___x_2599_);
                            if v___x_2600_ == 0 {
                                leanh::lean_dec(v_name_2598_);
                                leanh::lean_dec(v_toPure_2573_);
                                v___f_2601_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3
                                        as *mut core::ffi::c_void,
                                    2,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_2601_, 0, v___f_2590_);
                                v___f_2602_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__4___boxed
                                        as *mut core::ffi::c_void,
                                    6,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_2602_, 0, v_declName_2584_);
                                v___x_2603_ = leanh::lean_apply_2(
                                    v_inst_2520_,
                                    leanh::lean_box(0),
                                    v___f_2602_,
                                );
                                v___x_2604_ = leanh::lean_apply_4(
                                    v_toBind_2572_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2603_,
                                    v___f_2601_,
                                );
                                return v___x_2604_;
                            } else {
                                leanh::lean_dec(v_declName_2584_);
                                leanh::lean_dec(v_inst_2520_);
                                v___f_2605_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__3
                                        as *mut core::ffi::c_void,
                                    2,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_2605_, 0, v___f_2590_);
                                v___x_2606_ = l_Lean_TSyntax_getId(v_name_2598_);
                                leanh::lean_dec(v_name_2598_);
                                v___x_2607_ = leanh::lean_apply_2(
                                    v_toPure_2573_,
                                    leanh::lean_box(0),
                                    v___x_2606_,
                                );
                                v___x_2608_ = leanh::lean_apply_4(
                                    v_toBind_2572_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2607_,
                                    v___f_2605_,
                                );
                                return v___x_2608_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_hyps_2576_);
                        leanh::lean_dec_ref(v_00_u03c3s_2575_);
                        leanh::lean_dec(v_u_2574_);
                        leanh::lean_dec(v_k_2523_);
                        leanh::lean_dec(v_ident_2522_);
                        leanh::lean_dec_ref(v_inst_2519_);
                        v_isSharedCheck_2619_ =
                            (!leanh::lean_is_exclusive(v_inst_2518_)) as u8;
                        if v_isSharedCheck_2619_ == 0 {
                            v_unused_2620_ = leanh::lean_ctor_get(v_inst_2518_, 1);
                            leanh::lean_dec(v_unused_2620_);
                            v_unused_2621_ = leanh::lean_ctor_get(v_inst_2518_, 0);
                            leanh::lean_dec(v_unused_2621_);
                            v___x_2610_ = v_inst_2518_;
                            v_isShared_2611_ = v_isSharedCheck_2619_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_inst_2518_);
                            v___x_2610_ = leanh::lean_box(0);
                            v_isShared_2611_ = v_isSharedCheck_2619_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_toPure_2573_);
                    leanh::lean_inc_n(v_toBind_2572_, 2);
                    leanh::lean_dec_ref_known(v___x_2570_, 3);
                    leanh::lean_dec_ref(v_inst_2519_);
                    leanh::lean_dec_ref(v_inst_2518_);
                    v___f_2622_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__8___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2622_, 0, v_ident_2522_);
                    v___x_2623_ = l_Lean_Expr_appFn_x21(v_target_2577_);
                    v___x_2624_ = l_Lean_Expr_appFn_x21(v___x_2623_);
                    v___x_2625_ = l_Lean_Expr_appArg_x21(v___x_2624_);
                    leanh::lean_dec_ref(v___x_2624_);
                    v___x_2626_ = l_Lean_Expr_appArg_x21(v___x_2623_);
                    leanh::lean_dec_ref(v___x_2623_);
                    v___x_2627_ = l_Lean_Expr_appArg_x21(v_target_2577_);
                    leanh::lean_dec_ref(v_target_2577_);
                    v___x_2628_ = leanh::lean_box((v___x_2583_) as usize);
                    leanh::lean_inc(v_inst_2520_);
                    v___f_2629_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___lam__9___boxed
                            as *mut core::ffi::c_void,
                        17,
                        16,
                    );
                    leanh::lean_closure_set(v___f_2629_, 0, v___x_2626_);
                    leanh::lean_closure_set(v___f_2629_, 1, v_u_2574_);
                    leanh::lean_closure_set(v___f_2629_, 2, v_00_u03c3s_2575_);
                    leanh::lean_closure_set(v___f_2629_, 3, v_hyps_2576_);
                    leanh::lean_closure_set(v___f_2629_, 4, v___x_2578_);
                    leanh::lean_closure_set(v___f_2629_, 5, v___x_2579_);
                    leanh::lean_closure_set(v___f_2629_, 6, v___x_2580_);
                    leanh::lean_closure_set(v___f_2629_, 7, v___x_2625_);
                    leanh::lean_closure_set(v___f_2629_, 8, v___x_2627_);
                    leanh::lean_closure_set(v___f_2629_, 9, v_toPure_2573_);
                    leanh::lean_closure_set(v___f_2629_, 10, v_k_2523_);
                    leanh::lean_closure_set(v___f_2629_, 11, v_toBind_2572_);
                    leanh::lean_closure_set(v___f_2629_, 12, v___x_2628_);
                    leanh::lean_closure_set(v___f_2629_, 13, v_inst_2520_);
                    leanh::lean_closure_set(v___f_2629_, 14, v___x_2563_);
                    leanh::lean_closure_set(v___f_2629_, 15, v___x_2564_);
                    v___x_2630_ = leanh::lean_apply_2(
                        v_inst_2520_,
                        leanh::lean_box(0),
                        v___f_2622_,
                    );
                    v___x_2631_ = leanh::lean_apply_4(
                        v_toBind_2572_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2630_,
                        v___f_2629_,
                    );
                    return v___x_2631_;
                }
            }
            5 => {
                v___x_2612_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31,
                );
                v___x_2613_ = l_Lean_MessageData_ofExpr(v_target_2577_);
                if v_isShared_2611_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2610_, 7);
                    leanh::lean_ctor_set(v___x_2610_, 1, v___x_2613_);
                    leanh::lean_ctor_set(v___x_2610_, 0, v___x_2612_);
                    v___x_2615_ = v___x_2610_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2618_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2613_);
                    v___x_2615_ = v_reuseFailAlloc_2618_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2616_ = l_Lean_throwError___redArg(v___x_2563_, v___x_2570_, v___x_2615_);
                v___x_2617_ = leanh::lean_apply_2(
                    v_inst_2520_,
                    leanh::lean_box(0),
                    v___x_2616_,
                );
                return v___x_2617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro(
    mut v_m_2638_: *mut leanh::LeanObject,
    mut v_inst_2639_: *mut leanh::LeanObject,
    mut v_inst_2640_: *mut leanh::LeanObject,
    mut v_inst_2641_: *mut leanh::LeanObject,
    mut v_goal_2642_: *mut leanh::LeanObject,
    mut v_ident_2643_: *mut leanh::LeanObject,
    mut v_k_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2645_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg(
        v_inst_2639_,
        v_inst_2640_,
        v_inst_2641_,
        v_goal_2642_,
        v_ident_2643_,
        v_k_2644_,
    );
    return v___x_2645_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0(
    mut v_u_2652_: *mut leanh::LeanObject,
    mut v___x_2653_: *mut leanh::LeanObject,
    mut v___x_2654_: *mut leanh::LeanObject,
    mut v_hyps_2655_: *mut leanh::LeanObject,
    mut v_target_2656_: *mut leanh::LeanObject,
    mut v_toPure_2657_: *mut leanh::LeanObject,
    mut v_prf_2658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1;
    v___x_2660_ = leanh::lean_box(0);
    v___x_2661_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2661_, 0, v_u_2652_);
    leanh::lean_ctor_set(v___x_2661_, 1, v___x_2660_);
    v___x_2662_ = l_Lean_mkConst(v___x_2659_, v___x_2661_);
    v___x_2663_ = l_Lean_mkApp5(
        v___x_2662_,
        v___x_2653_,
        v___x_2654_,
        v_hyps_2655_,
        v_target_2656_,
        v_prf_2658_,
    );
    v___x_2664_ =
        leanh::lean_apply_2(v_toPure_2657_, leanh::lean_box(0), v___x_2663_);
    return v___x_2664_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(
    mut v___x_2665_: *mut leanh::LeanObject,
    mut v___x_2666_: u8,
    mut v___x_2667_: u8,
    mut v_inst_2668_: *mut leanh::LeanObject,
    mut v_toBind_2669_: *mut leanh::LeanObject,
    mut v___f_2670_: *mut leanh::LeanObject,
    mut v_prf_2671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2672_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2672_ = 1;
    v___x_2673_ = leanh::lean_box((v___x_2666_) as usize);
    v___x_2674_ = leanh::lean_box((v___x_2667_) as usize);
    v___x_2675_ = leanh::lean_box((v___x_2666_) as usize);
    v___x_2676_ = leanh::lean_box((v___x_2667_) as usize);
    v___x_2677_ = leanh::lean_box((v___x_2672_) as usize);
    v___x_2678_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_2678_, 0, v___x_2665_);
    leanh::lean_closure_set(v___x_2678_, 1, v_prf_2671_);
    leanh::lean_closure_set(v___x_2678_, 2, v___x_2673_);
    leanh::lean_closure_set(v___x_2678_, 3, v___x_2674_);
    leanh::lean_closure_set(v___x_2678_, 4, v___x_2675_);
    leanh::lean_closure_set(v___x_2678_, 5, v___x_2676_);
    leanh::lean_closure_set(v___x_2678_, 6, v___x_2677_);
    v___x_2679_ = leanh::lean_apply_2(v_inst_2668_, leanh::lean_box(0), v___x_2678_);
    v___x_2680_ = leanh::lean_apply_4(
        v_toBind_2669_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2679_,
        v___f_2670_,
    );
    return v___x_2680_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed(
    mut v___x_2681_: *mut leanh::LeanObject,
    mut v___x_2682_: *mut leanh::LeanObject,
    mut v___x_2683_: *mut leanh::LeanObject,
    mut v_inst_2684_: *mut leanh::LeanObject,
    mut v_toBind_2685_: *mut leanh::LeanObject,
    mut v___f_2686_: *mut leanh::LeanObject,
    mut v_prf_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2265__boxed_2688_: u8 = 0;
    let mut v___x_2266__boxed_2689_: u8 = 0;
    let mut v_res_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2265__boxed_2688_ = (leanh::lean_unbox(v___x_2682_) as u8);
    v___x_2266__boxed_2689_ = (leanh::lean_unbox(v___x_2683_) as u8);
    v_res_2690_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1(
        v___x_2681_,
        v___x_2265__boxed_2688_,
        v___x_2266__boxed_2689_,
        v_inst_2684_,
        v_toBind_2685_,
        v___f_2686_,
        v_prf_2687_,
    );
    return v_res_2690_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(
    mut v___x_2691_: *mut leanh::LeanObject,
    mut v_ident_2692_: *mut leanh::LeanObject,
    mut v___x_2693_: u8,
    mut v_hyps_2694_: *mut leanh::LeanObject,
    mut v___x_2695_: *mut leanh::LeanObject,
    mut v_inst_2696_: *mut leanh::LeanObject,
    mut v_toBind_2697_: *mut leanh::LeanObject,
    mut v___f_2698_: *mut leanh::LeanObject,
    mut v_target_2699_: *mut leanh::LeanObject,
    mut v_u_2700_: *mut leanh::LeanObject,
    mut v_k_2701_: *mut leanh::LeanObject,
    mut v_map_2702_: *mut leanh::LeanObject,
    mut v_s_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_2709_ = leanh::lean_ctor_get(v___y_2704_, 2);
                v___x_2710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2710_, 0, v___x_2691_);
                leanh::lean_inc_ref(v_s_2703_);
                leanh::lean_inc_ref(v_lctx_2709_);
                v___x_2711_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                    v_ident_2692_,
                    v_lctx_2709_,
                    v_s_2703_,
                    v___x_2710_,
                    v___x_2693_,
                    v___y_2704_,
                    v___y_2705_,
                    v___y_2706_,
                    v___y_2707_,
                );
                if leanh::lean_obj_tag(v___x_2711_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2711_, 1);
                    leanh::lean_inc_ref(v_s_2703_);
                    v___x_2712_ = l_Lean_Expr_app___override(v_hyps_2694_, v_s_2703_);
                    leanh::lean_inc_ref(v___x_2695_);
                    v___x_2713_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
                        v___x_2695_,
                        v___x_2712_,
                    );
                    v___x_2714_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2714_);
                    v___x_2716_ = lean_array_push(v___x_2715_, v_s_2703_);
                    v___x_2717_ = 0;
                    v___x_2718_ = leanh::lean_box((v___x_2717_) as usize);
                    v___x_2719_ = leanh::lean_box((v___x_2693_) as usize);
                    leanh::lean_inc(v_toBind_2697_);
                    leanh::lean_inc_ref(v___x_2716_);
                    v___f_2720_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        6,
                    );
                    leanh::lean_closure_set(v___f_2720_, 0, v___x_2716_);
                    leanh::lean_closure_set(v___f_2720_, 1, v___x_2718_);
                    leanh::lean_closure_set(v___f_2720_, 2, v___x_2719_);
                    leanh::lean_closure_set(v___f_2720_, 3, v_inst_2696_);
                    leanh::lean_closure_set(v___f_2720_, 4, v_toBind_2697_);
                    leanh::lean_closure_set(v___f_2720_, 5, v___f_2698_);
                    v___x_2721_ =
                        l_Lean_Expr_betaRev(v_target_2699_, v___x_2716_, v___x_2717_, v___x_2717_);
                    leanh::lean_dec_ref(v___x_2716_);
                    v___x_2722_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_2722_, 0, v_u_2700_);
                    leanh::lean_ctor_set(v___x_2722_, 1, v___x_2695_);
                    leanh::lean_ctor_set(v___x_2722_, 2, v___x_2713_);
                    leanh::lean_ctor_set(v___x_2722_, 3, v___x_2721_);
                    v___x_2723_ = leanh::lean_apply_1(v_k_2701_, v___x_2722_);
                    v___x_2724_ = leanh::lean_apply_4(
                        v_toBind_2697_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2723_,
                        v___f_2720_,
                    );
                    leanh::lean_inc(v___y_2707_);
                    leanh::lean_inc_ref(v___y_2706_);
                    leanh::lean_inc(v___y_2705_);
                    leanh::lean_inc_ref(v___y_2704_);
                    v___x_2725_ = leanh::lean_apply_7(
                        v_map_2702_,
                        leanh::lean_box(0),
                        v___x_2724_,
                        v___y_2704_,
                        v___y_2705_,
                        v___y_2706_,
                        v___y_2707_,
                        leanh::lean_box(0),
                    );
                    return v___x_2725_;
                } else {
                    leanh::lean_dec_ref(v_s_2703_);
                    leanh::lean_dec_ref(v_map_2702_);
                    leanh::lean_dec(v_k_2701_);
                    leanh::lean_dec(v_u_2700_);
                    leanh::lean_dec_ref(v_target_2699_);
                    leanh::lean_dec(v___f_2698_);
                    leanh::lean_dec(v_toBind_2697_);
                    leanh::lean_dec(v_inst_2696_);
                    leanh::lean_dec_ref(v___x_2695_);
                    leanh::lean_dec_ref(v_hyps_2694_);
                    v_a_2726_ = leanh::lean_ctor_get(v___x_2711_, 0);
                    v_isSharedCheck_2733_ = (!leanh::lean_is_exclusive(v___x_2711_)) as u8;
                    if v_isSharedCheck_2733_ == 0 {
                        v___x_2728_ = v___x_2711_;
                        v_isShared_2729_ = v_isSharedCheck_2733_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2726_);
                        leanh::lean_dec(v___x_2711_);
                        v___x_2728_ = leanh::lean_box(0);
                        v_isShared_2729_ = v_isSharedCheck_2733_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2729_ == 0 {
                    v___x_2731_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2734_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ident_2735_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_2736_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_hyps_2737_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2738_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_2739_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2740_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_2741_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_target_2742_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_u_2743_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_k_2744_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_map_2745_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_s_2746_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_2747_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_2748_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_2749_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2750_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_2751_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_2298__boxed_2752_: u8 = 0;
    let mut v_res_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2298__boxed_2752_ = (leanh::lean_unbox(v___x_2736_) as u8);
    v_res_2753_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2(
        v___x_2734_,
        v_ident_2735_,
        v___x_2298__boxed_2752_,
        v_hyps_2737_,
        v___x_2738_,
        v_inst_2739_,
        v_toBind_2740_,
        v___f_2741_,
        v_target_2742_,
        v_u_2743_,
        v_k_2744_,
        v_map_2745_,
        v_s_2746_,
        v___y_2747_,
        v___y_2748_,
        v___y_2749_,
        v___y_2750_,
    );
    leanh::lean_dec(v___y_2750_);
    leanh::lean_dec_ref(v___y_2749_);
    leanh::lean_dec(v___y_2748_);
    leanh::lean_dec_ref(v___y_2747_);
    return v_res_2753_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2760_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__3;
    v___x_2761_ = l_Lean_stringToMessageData(v___x_2760_);
    return v___x_2761_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(
    mut v_goal_2765_: *mut leanh::LeanObject,
    mut v___x_2766_: *mut leanh::LeanObject,
    mut v___x_2767_: *mut leanh::LeanObject,
    mut v_toPure_2768_: *mut leanh::LeanObject,
    mut v_ident_2769_: *mut leanh::LeanObject,
    mut v_inst_2770_: *mut leanh::LeanObject,
    mut v_toBind_2771_: *mut leanh::LeanObject,
    mut v_k_2772_: *mut leanh::LeanObject,
    mut v___x_2773_: *mut leanh::LeanObject,
    mut v_map_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
    mut v___y_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
    mut v___y_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189__overap_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204__overap_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: u8 = 0;
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218__overap_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223__overap_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2838_: u8 = 0;
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2780_ = leanh::lean_ctor_get(v_goal_2765_, 0);
                leanh::lean_inc(v_u_2780_);
                v_00_u03c3s_2781_ = leanh::lean_ctor_get(v_goal_2765_, 1);
                leanh::lean_inc_ref_n(v_00_u03c3s_2781_, 2);
                v_hyps_2782_ = leanh::lean_ctor_get(v_goal_2765_, 2);
                leanh::lean_inc_ref(v_hyps_2782_);
                v_target_2783_ = leanh::lean_ctor_get(v_goal_2765_, 3);
                leanh::lean_inc_ref(v_target_2783_);
                leanh::lean_dec_ref(v_goal_2765_);
                leanh::lean_inc(v___y_2778_);
                leanh::lean_inc_ref(v___y_2777_);
                leanh::lean_inc(v___y_2776_);
                leanh::lean_inc_ref(v___y_2775_);
                v___x_2784_ = lean_whnf(
                    v_00_u03c3s_2781_,
                    v___y_2775_,
                    v___y_2776_,
                    v___y_2777_,
                    v___y_2778_,
                );
                if leanh::lean_obj_tag(v___x_2784_) == 0 {
                    v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    leanh::lean_inc(v_a_2785_);
                    leanh::lean_dec_ref_known(v___x_2784_, 1);
                    v___x_2786_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2;
                    v___x_2787_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2788_ = l_Lean_Expr_isAppOfArity(v_a_2785_, v___x_2786_, v___x_2787_);
                    if v___x_2788_ == 0 {
                        leanh::lean_dec(v_a_2785_);
                        leanh::lean_dec_ref(v_target_2783_);
                        leanh::lean_dec_ref(v_hyps_2782_);
                        leanh::lean_dec(v_u_2780_);
                        leanh::lean_dec_ref(v_map_2774_);
                        leanh::lean_dec_ref(v___x_2773_);
                        leanh::lean_dec(v_k_2772_);
                        leanh::lean_dec(v_toBind_2771_);
                        leanh::lean_dec(v_inst_2770_);
                        leanh::lean_dec(v_ident_2769_);
                        leanh::lean_dec(v_toPure_2768_);
                        v___x_2789_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
                        v___x_2790_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_2781_);
                        v___x_2791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2791_, 0, v___x_2789_);
                        leanh::lean_ctor_set(v___x_2791_, 1, v___x_2790_);
                        v___x_2189__overap_2792_ =
                            l_Lean_throwError___redArg(v___x_2766_, v___x_2767_, v___x_2791_);
                        leanh::lean_inc(v___y_2778_);
                        leanh::lean_inc_ref(v___y_2777_);
                        leanh::lean_inc(v___y_2776_);
                        leanh::lean_inc_ref(v___y_2775_);
                        v___x_2793_ = leanh::lean_apply_5(
                            v___x_2189__overap_2792_,
                            v___y_2775_,
                            v___y_2776_,
                            v___y_2777_,
                            v___y_2778_,
                            leanh::lean_box(0),
                        );
                        return v___x_2793_;
                    } else {
                        leanh::lean_dec_ref(v_00_u03c3s_2781_);
                        leanh::lean_dec_ref(v___x_2767_);
                        v___x_2794_ = l_Lean_Expr_appFn_x21(v_a_2785_);
                        v___x_2795_ = l_Lean_Expr_appArg_x21(v___x_2794_);
                        leanh::lean_dec_ref(v___x_2794_);
                        v___x_2796_ = l_Lean_Expr_appArg_x21(v_a_2785_);
                        leanh::lean_dec(v_a_2785_);
                        leanh::lean_inc_ref(v_target_2783_);
                        leanh::lean_inc_ref(v_hyps_2782_);
                        leanh::lean_inc_ref_n(v___x_2795_, 2);
                        leanh::lean_inc_ref(v___x_2796_);
                        leanh::lean_inc(v_u_2780_);
                        v___f_2797_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        leanh::lean_closure_set(v___f_2797_, 0, v_u_2780_);
                        leanh::lean_closure_set(v___f_2797_, 1, v___x_2796_);
                        leanh::lean_closure_set(v___f_2797_, 2, v___x_2795_);
                        leanh::lean_closure_set(v___f_2797_, 3, v_hyps_2782_);
                        leanh::lean_closure_set(v___f_2797_, 4, v_target_2783_);
                        leanh::lean_closure_set(v___f_2797_, 5, v_toPure_2768_);
                        v___x_2798_ = leanh::lean_box((v___x_2788_) as usize);
                        leanh::lean_inc_n(v_ident_2769_, 2);
                        v___f_2799_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__2___boxed
                                as *mut core::ffi::c_void,
                            18,
                            12,
                        );
                        leanh::lean_closure_set(v___f_2799_, 0, v___x_2795_);
                        leanh::lean_closure_set(v___f_2799_, 1, v_ident_2769_);
                        leanh::lean_closure_set(v___f_2799_, 2, v___x_2798_);
                        leanh::lean_closure_set(v___f_2799_, 3, v_hyps_2782_);
                        leanh::lean_closure_set(v___f_2799_, 4, v___x_2796_);
                        leanh::lean_closure_set(v___f_2799_, 5, v_inst_2770_);
                        leanh::lean_closure_set(v___f_2799_, 6, v_toBind_2771_);
                        leanh::lean_closure_set(v___f_2799_, 7, v___f_2797_);
                        leanh::lean_closure_set(v___f_2799_, 8, v_target_2783_);
                        leanh::lean_closure_set(v___f_2799_, 9, v_u_2780_);
                        leanh::lean_closure_set(v___f_2799_, 10, v_k_2772_);
                        leanh::lean_closure_set(v___f_2799_, 11, v_map_2774_);
                        v___x_2800_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        v___x_2801_ = l_Lean_Syntax_isOfKind(v_ident_2769_, v___x_2800_);
                        if v___x_2801_ == 0 {
                            leanh::lean_dec(v_ident_2769_);
                            v___x_2802_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6;
                            v___x_2803_ =
                                l_Lean_Core_mkFreshUserName(v___x_2802_, v___y_2777_, v___y_2778_);
                            if leanh::lean_obj_tag(v___x_2803_) == 0 {
                                v_a_2804_ = leanh::lean_ctor_get(v___x_2803_, 0);
                                leanh::lean_inc(v_a_2804_);
                                leanh::lean_dec_ref_known(v___x_2803_, 1);
                                v___x_2204__overap_2805_ = l_Lean_Meta_withLocalDeclD___redArg(
                                    v___x_2773_,
                                    v___x_2766_,
                                    v_a_2804_,
                                    v___x_2795_,
                                    v___f_2799_,
                                );
                                leanh::lean_inc(v___y_2778_);
                                leanh::lean_inc_ref(v___y_2777_);
                                leanh::lean_inc(v___y_2776_);
                                leanh::lean_inc_ref(v___y_2775_);
                                v___x_2806_ = leanh::lean_apply_5(
                                    v___x_2204__overap_2805_,
                                    v___y_2775_,
                                    v___y_2776_,
                                    v___y_2777_,
                                    v___y_2778_,
                                    leanh::lean_box(0),
                                );
                                return v___x_2806_;
                            } else {
                                leanh::lean_dec_ref(v___f_2799_);
                                leanh::lean_dec_ref(v___x_2795_);
                                leanh::lean_dec_ref(v___x_2773_);
                                leanh::lean_dec_ref(v___x_2766_);
                                v_a_2807_ = leanh::lean_ctor_get(v___x_2803_, 0);
                                v_isSharedCheck_2814_ =
                                    (!leanh::lean_is_exclusive(v___x_2803_)) as u8;
                                if v_isSharedCheck_2814_ == 0 {
                                    v___x_2809_ = v___x_2803_;
                                    v_isShared_2810_ = v_isSharedCheck_2814_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2807_);
                                    leanh::lean_dec(v___x_2803_);
                                    v___x_2809_ = leanh::lean_box(0);
                                    v_isShared_2810_ = v_isSharedCheck_2814_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2815_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2816_ = l_Lean_Syntax_getArg(v_ident_2769_, v___x_2815_);
                            leanh::lean_dec(v_ident_2769_);
                            v___x_2817_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29;
                            leanh::lean_inc(v___x_2816_);
                            v___x_2818_ = l_Lean_Syntax_isOfKind(v___x_2816_, v___x_2817_);
                            if v___x_2818_ == 0 {
                                leanh::lean_dec(v___x_2816_);
                                v___x_2819_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6;
                                v___x_2820_ = l_Lean_Core_mkFreshUserName(
                                    v___x_2819_,
                                    v___y_2777_,
                                    v___y_2778_,
                                );
                                if leanh::lean_obj_tag(v___x_2820_) == 0 {
                                    v_a_2821_ = leanh::lean_ctor_get(v___x_2820_, 0);
                                    leanh::lean_inc(v_a_2821_);
                                    leanh::lean_dec_ref_known(v___x_2820_, 1);
                                    v___x_2218__overap_2822_ = l_Lean_Meta_withLocalDeclD___redArg(
                                        v___x_2773_,
                                        v___x_2766_,
                                        v_a_2821_,
                                        v___x_2795_,
                                        v___f_2799_,
                                    );
                                    leanh::lean_inc(v___y_2778_);
                                    leanh::lean_inc_ref(v___y_2777_);
                                    leanh::lean_inc(v___y_2776_);
                                    leanh::lean_inc_ref(v___y_2775_);
                                    v___x_2823_ = leanh::lean_apply_5(
                                        v___x_2218__overap_2822_,
                                        v___y_2775_,
                                        v___y_2776_,
                                        v___y_2777_,
                                        v___y_2778_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_2823_;
                                } else {
                                    leanh::lean_dec_ref(v___f_2799_);
                                    leanh::lean_dec_ref(v___x_2795_);
                                    leanh::lean_dec_ref(v___x_2773_);
                                    leanh::lean_dec_ref(v___x_2766_);
                                    v_a_2824_ = leanh::lean_ctor_get(v___x_2820_, 0);
                                    v_isSharedCheck_2831_ =
                                        (!leanh::lean_is_exclusive(v___x_2820_)) as u8;
                                    if v_isSharedCheck_2831_ == 0 {
                                        v___x_2826_ = v___x_2820_;
                                        v_isShared_2827_ = v_isSharedCheck_2831_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2824_);
                                        leanh::lean_dec(v___x_2820_);
                                        v___x_2826_ = leanh::lean_box(0);
                                        v_isShared_2827_ = v_isSharedCheck_2831_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_2832_ = l_Lean_TSyntax_getId(v___x_2816_);
                                leanh::lean_dec(v___x_2816_);
                                v___x_2223__overap_2833_ = l_Lean_Meta_withLocalDeclD___redArg(
                                    v___x_2773_,
                                    v___x_2766_,
                                    v___x_2832_,
                                    v___x_2795_,
                                    v___f_2799_,
                                );
                                leanh::lean_inc(v___y_2778_);
                                leanh::lean_inc_ref(v___y_2777_);
                                leanh::lean_inc(v___y_2776_);
                                leanh::lean_inc_ref(v___y_2775_);
                                v___x_2834_ = leanh::lean_apply_5(
                                    v___x_2223__overap_2833_,
                                    v___y_2775_,
                                    v___y_2776_,
                                    v___y_2777_,
                                    v___y_2778_,
                                    leanh::lean_box(0),
                                );
                                return v___x_2834_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_target_2783_);
                    leanh::lean_dec_ref(v_hyps_2782_);
                    leanh::lean_dec_ref(v_00_u03c3s_2781_);
                    leanh::lean_dec(v_u_2780_);
                    leanh::lean_dec_ref(v_map_2774_);
                    leanh::lean_dec_ref(v___x_2773_);
                    leanh::lean_dec(v_k_2772_);
                    leanh::lean_dec(v_toBind_2771_);
                    leanh::lean_dec(v_inst_2770_);
                    leanh::lean_dec(v_ident_2769_);
                    leanh::lean_dec(v_toPure_2768_);
                    leanh::lean_dec_ref(v___x_2767_);
                    leanh::lean_dec_ref(v___x_2766_);
                    v_a_2835_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2842_ = (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2842_ == 0 {
                        v___x_2837_ = v___x_2784_;
                        v_isShared_2838_ = v_isSharedCheck_2842_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2835_);
                        leanh::lean_dec(v___x_2784_);
                        v___x_2837_ = leanh::lean_box(0);
                        v_isShared_2838_ = v_isSharedCheck_2842_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2810_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2812_;
            }
            3 => {
                if v_isShared_2827_ == 0 {
                    v___x_2829_ = v___x_2826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2829_;
            }
            5 => {
                if v_isShared_2838_ == 0 {
                    v___x_2840_ = v___x_2837_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
                    v___x_2840_ = v_reuseFailAlloc_2841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed(
    mut v_goal_2843_: *mut leanh::LeanObject,
    mut v___x_2844_: *mut leanh::LeanObject,
    mut v___x_2845_: *mut leanh::LeanObject,
    mut v_toPure_2846_: *mut leanh::LeanObject,
    mut v_ident_2847_: *mut leanh::LeanObject,
    mut v_inst_2848_: *mut leanh::LeanObject,
    mut v_toBind_2849_: *mut leanh::LeanObject,
    mut v_k_2850_: *mut leanh::LeanObject,
    mut v___x_2851_: *mut leanh::LeanObject,
    mut v_map_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3(
        v_goal_2843_,
        v___x_2844_,
        v___x_2845_,
        v_toPure_2846_,
        v_ident_2847_,
        v_inst_2848_,
        v_toBind_2849_,
        v_k_2850_,
        v___x_2851_,
        v_map_2852_,
        v___y_2853_,
        v___y_2854_,
        v___y_2855_,
        v___y_2856_,
    );
    leanh::lean_dec(v___y_2856_);
    leanh::lean_dec_ref(v___y_2855_);
    leanh::lean_dec(v___y_2854_);
    leanh::lean_dec_ref(v___y_2853_);
    return v_res_2858_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(
    mut v_inst_2859_: *mut leanh::LeanObject,
    mut v_inst_2860_: *mut leanh::LeanObject,
    mut v_inst_2861_: *mut leanh::LeanObject,
    mut v_goal_2862_: *mut leanh::LeanObject,
    mut v_ident_2863_: *mut leanh::LeanObject,
    mut v_k_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v_toFunctor_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___f_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_liftWith_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2938_: u8 = 0;
    let mut v_unused_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2940_: u8 = 0;
    let mut v_unused_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2865_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__1,
                );
                v_toApplicative_2866_ = leanh::lean_ctor_get(v___x_2865_, 0);
                v_toFunctor_2867_ = leanh::lean_ctor_get(v_toApplicative_2866_, 0);
                v_toSeq_2868_ = leanh::lean_ctor_get(v_toApplicative_2866_, 2);
                v_toSeqLeft_2869_ = leanh::lean_ctor_get(v_toApplicative_2866_, 3);
                v_toSeqRight_2870_ = leanh::lean_ctor_get(v_toApplicative_2866_, 4);
                v___f_2871_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__2;
                v___f_2872_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2867_, 2);
                v___f_2873_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2873_, 0, v_toFunctor_2867_);
                v___f_2874_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2874_, 0, v_toFunctor_2867_);
                v___x_2875_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2875_, 0, v___f_2873_);
                leanh::lean_ctor_set(v___x_2875_, 1, v___f_2874_);
                leanh::lean_inc(v_toSeqRight_2870_);
                v___f_2876_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2876_, 0, v_toSeqRight_2870_);
                leanh::lean_inc(v_toSeqLeft_2869_);
                v___f_2877_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2877_, 0, v_toSeqLeft_2869_);
                leanh::lean_inc(v_toSeq_2868_);
                v___f_2878_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2878_, 0, v_toSeq_2868_);
                v___x_2879_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2879_, 0, v___x_2875_);
                leanh::lean_ctor_set(v___x_2879_, 1, v___f_2871_);
                leanh::lean_ctor_set(v___x_2879_, 2, v___f_2878_);
                leanh::lean_ctor_set(v___x_2879_, 3, v___f_2877_);
                leanh::lean_ctor_set(v___x_2879_, 4, v___f_2876_);
                v___x_2880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2880_, 1, v___f_2872_);
                v___x_2881_ = l_StateRefT_x27_instMonad___redArg(v___x_2880_);
                v_toApplicative_2882_ = leanh::lean_ctor_get(v___x_2881_, 0);
                v_isSharedCheck_2940_ = (!leanh::lean_is_exclusive(v___x_2881_)) as u8;
                if v_isSharedCheck_2940_ == 0 {
                    v_unused_2941_ = leanh::lean_ctor_get(v___x_2881_, 1);
                    leanh::lean_dec(v_unused_2941_);
                    v___x_2884_ = v___x_2881_;
                    v_isShared_2885_ = v_isSharedCheck_2940_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2882_);
                    leanh::lean_dec(v___x_2881_);
                    v___x_2884_ = leanh::lean_box(0);
                    v_isShared_2885_ = v_isSharedCheck_2940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2886_ = leanh::lean_ctor_get(v_toApplicative_2882_, 0);
                v_toSeq_2887_ = leanh::lean_ctor_get(v_toApplicative_2882_, 2);
                v_toSeqLeft_2888_ = leanh::lean_ctor_get(v_toApplicative_2882_, 3);
                v_toSeqRight_2889_ = leanh::lean_ctor_get(v_toApplicative_2882_, 4);
                v_isSharedCheck_2938_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2882_)) as u8;
                if v_isSharedCheck_2938_ == 0 {
                    v_unused_2939_ = leanh::lean_ctor_get(v_toApplicative_2882_, 1);
                    leanh::lean_dec(v_unused_2939_);
                    v___x_2891_ = v_toApplicative_2882_;
                    v_isShared_2892_ = v_isSharedCheck_2938_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2889_);
                    leanh::lean_inc(v_toSeqLeft_2888_);
                    leanh::lean_inc(v_toSeq_2887_);
                    leanh::lean_inc(v_toFunctor_2886_);
                    leanh::lean_dec(v_toApplicative_2882_);
                    v___x_2891_ = leanh::lean_box(0);
                    v_isShared_2892_ = v_isSharedCheck_2938_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2893_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__6;
                v___f_2894_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__7;
                leanh::lean_inc_ref(v_toFunctor_2886_);
                v___f_2895_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2895_, 0, v_toFunctor_2886_);
                v___f_2896_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2896_, 0, v_toFunctor_2886_);
                v___x_2897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2897_, 0, v___f_2895_);
                leanh::lean_ctor_set(v___x_2897_, 1, v___f_2896_);
                v___f_2898_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2898_, 0, v_toSeqRight_2889_);
                v___f_2899_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2899_, 0, v_toSeqLeft_2888_);
                v___f_2900_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2900_, 0, v_toSeq_2887_);
                if v_isShared_2892_ == 0 {
                    leanh::lean_ctor_set(v___x_2891_, 4, v___f_2898_);
                    leanh::lean_ctor_set(v___x_2891_, 3, v___f_2899_);
                    leanh::lean_ctor_set(v___x_2891_, 2, v___f_2900_);
                    leanh::lean_ctor_set(v___x_2891_, 1, v___f_2893_);
                    leanh::lean_ctor_set(v___x_2891_, 0, v___x_2897_);
                    v___x_2902_ = v___x_2891_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2937_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 1, v___f_2893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 2, v___f_2900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 3, v___f_2899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2937_, 4, v___f_2898_);
                    v___x_2902_ = v_reuseFailAlloc_2937_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2885_ == 0 {
                    leanh::lean_ctor_set(v___x_2884_, 1, v___f_2894_);
                    leanh::lean_ctor_set(v___x_2884_, 0, v___x_2902_);
                    v___x_2904_ = v___x_2884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2936_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___f_2894_);
                    v___x_2904_ = v_reuseFailAlloc_2936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_toApplicative_2905_ = leanh::lean_ctor_get(v___x_2865_, 0);
                v_toFunctor_2906_ = leanh::lean_ctor_get(v_toApplicative_2905_, 0);
                v_toSeq_2907_ = leanh::lean_ctor_get(v_toApplicative_2905_, 2);
                v_toSeqLeft_2908_ = leanh::lean_ctor_get(v_toApplicative_2905_, 3);
                v_toSeqRight_2909_ = leanh::lean_ctor_get(v_toApplicative_2905_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2906_, 2);
                v___f_2910_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2910_, 0, v_toFunctor_2906_);
                v___f_2911_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2911_, 0, v_toFunctor_2906_);
                v___x_2912_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2912_, 0, v___f_2910_);
                leanh::lean_ctor_set(v___x_2912_, 1, v___f_2911_);
                leanh::lean_inc(v_toSeqRight_2909_);
                v___f_2913_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2913_, 0, v_toSeqRight_2909_);
                leanh::lean_inc(v_toSeqLeft_2908_);
                v___f_2914_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2914_, 0, v_toSeqLeft_2908_);
                leanh::lean_inc(v_toSeq_2907_);
                v___f_2915_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2915_, 0, v_toSeq_2907_);
                v___x_2916_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2916_, 0, v___x_2912_);
                leanh::lean_ctor_set(v___x_2916_, 1, v___f_2871_);
                leanh::lean_ctor_set(v___x_2916_, 2, v___f_2915_);
                leanh::lean_ctor_set(v___x_2916_, 3, v___f_2914_);
                leanh::lean_ctor_set(v___x_2916_, 4, v___f_2913_);
                v___x_2917_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2917_, 0, v___x_2916_);
                leanh::lean_ctor_set(v___x_2917_, 1, v___f_2872_);
                v___x_2918_ = l_StateRefT_x27_instMonad___redArg(v___x_2917_);
                v___x_2919_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2919_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2919_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2919_, 2, v___x_2918_);
                v___x_2920_ = l_instMonadControlTOfPure___redArg(v___x_2919_);
                v___x_2921_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__15,
                );
                v___x_2922_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__19,
                );
                v_toMonadRef_2923_ = leanh::lean_ctor_get(v___x_2922_, 0);
                v___x_2924_ = l_Lean_Meta_instAddMessageContextMetaM;
                leanh::lean_inc_ref(v___x_2904_);
                v___x_2925_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___x_2924_,
                    v___x_2904_,
                );
                leanh::lean_inc_ref(v_toMonadRef_2923_);
                v___x_2926_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2926_, 0, v___x_2921_);
                leanh::lean_ctor_set(v___x_2926_, 1, v_toMonadRef_2923_);
                leanh::lean_ctor_set(v___x_2926_, 2, v___x_2925_);
                v_toApplicative_2927_ = leanh::lean_ctor_get(v_inst_2859_, 0);
                leanh::lean_inc_ref(v_toApplicative_2927_);
                v_toBind_2928_ = leanh::lean_ctor_get(v_inst_2859_, 1);
                leanh::lean_inc_n(v_toBind_2928_, 2);
                leanh::lean_dec_ref(v_inst_2859_);
                v_toPure_2929_ = leanh::lean_ctor_get(v_toApplicative_2927_, 1);
                leanh::lean_inc(v_toPure_2929_);
                leanh::lean_dec_ref(v_toApplicative_2927_);
                v_liftWith_2930_ = leanh::lean_ctor_get(v_inst_2860_, 0);
                leanh::lean_inc(v_liftWith_2930_);
                v_restoreM_2931_ = leanh::lean_ctor_get(v_inst_2860_, 1);
                leanh::lean_inc(v_restoreM_2931_);
                leanh::lean_dec_ref(v_inst_2860_);
                v___f_2932_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    15,
                    9,
                );
                leanh::lean_closure_set(v___f_2932_, 0, v_goal_2862_);
                leanh::lean_closure_set(v___f_2932_, 1, v___x_2904_);
                leanh::lean_closure_set(v___f_2932_, 2, v___x_2926_);
                leanh::lean_closure_set(v___f_2932_, 3, v_toPure_2929_);
                leanh::lean_closure_set(v___f_2932_, 4, v_ident_2863_);
                leanh::lean_closure_set(v___f_2932_, 5, v_inst_2861_);
                leanh::lean_closure_set(v___f_2932_, 6, v_toBind_2928_);
                leanh::lean_closure_set(v___f_2932_, 7, v_k_2864_);
                leanh::lean_closure_set(v___f_2932_, 8, v___x_2920_);
                v___x_2933_ = leanh::lean_apply_2(
                    v_liftWith_2930_,
                    leanh::lean_box(0),
                    v___f_2932_,
                );
                v___x_2934_ =
                    leanh::lean_apply_1(v_restoreM_2931_, leanh::lean_box(0));
                v___x_2935_ = leanh::lean_apply_4(
                    v_toBind_2928_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2933_,
                    v___x_2934_,
                );
                return v___x_2935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall(
    mut v_m_2942_: *mut leanh::LeanObject,
    mut v_inst_2943_: *mut leanh::LeanObject,
    mut v_inst_2944_: *mut leanh::LeanObject,
    mut v_inst_2945_: *mut leanh::LeanObject,
    mut v_goal_2946_: *mut leanh::LeanObject,
    mut v_ident_2947_: *mut leanh::LeanObject,
    mut v_k_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(
        v_inst_2943_,
        v_inst_2944_,
        v_inst_2945_,
        v_goal_2946_,
        v_ident_2947_,
        v_k_2948_,
    );
    return v___x_2949_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(
    mut v_isZero_2959_: u8,
    mut v___y_2960_: *mut leanh::LeanObject,
    mut v___y_2961_: *mut leanh::LeanObject,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2965_ = leanh::lean_ctor_get(v___y_2962_, 5);
    v___x_2966_ = l_Lean_SourceInfo_fromRef(v_ref_2965_, v_isZero_2959_);
    v___x_2967_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
    v___x_2968_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__3;
    v___x_2969_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___closed__4;
    leanh::lean_inc_n(v___x_2966_, 2);
    v___x_2970_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2970_, 0, v___x_2966_);
    leanh::lean_ctor_set(v___x_2970_, 1, v___x_2969_);
    v___x_2971_ = l_Lean_Syntax_node1(v___x_2966_, v___x_2968_, v___x_2970_);
    v___x_2972_ = l_Lean_Syntax_node1(v___x_2966_, v___x_2967_, v___x_2971_);
    v___x_2973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2973_, 0, v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed(
    mut v_isZero_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
    mut v___y_2977_: *mut leanh::LeanObject,
    mut v___y_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isZero_boxed_2980_: u8 = 0;
    let mut v_res_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_2980_ = (leanh::lean_unbox(v_isZero_2974_) as u8);
    v_res_2981_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0(
        v_isZero_boxed_2980_,
        v___y_2975_,
        v___y_2976_,
        v___y_2977_,
        v___y_2978_,
    );
    leanh::lean_dec(v___y_2978_);
    leanh::lean_dec_ref(v___y_2977_);
    leanh::lean_dec(v___y_2976_);
    leanh::lean_dec_ref(v___y_2975_);
    return v_res_2981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2(
    mut v_inst_2982_: *mut leanh::LeanObject,
    mut v_inst_2983_: *mut leanh::LeanObject,
    mut v_inst_2984_: *mut leanh::LeanObject,
    mut v_goal_2985_: *mut leanh::LeanObject,
    mut v___f_2986_: *mut leanh::LeanObject,
    mut v_____do__lift_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2988_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg(
        v_inst_2982_,
        v_inst_2983_,
        v_inst_2984_,
        v_goal_2985_,
        v_____do__lift_2987_,
        v___f_2986_,
    );
    return v___x_2988_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed(
    mut v_inst_2989_: *mut leanh::LeanObject,
    mut v_inst_2990_: *mut leanh::LeanObject,
    mut v_inst_2991_: *mut leanh::LeanObject,
    mut v_n_2992_: *mut leanh::LeanObject,
    mut v_k_2993_: *mut leanh::LeanObject,
    mut v_g_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2995_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(
        v_inst_2989_,
        v_inst_2990_,
        v_inst_2991_,
        v_n_2992_,
        v_k_2993_,
        v_g_2994_,
    );
    leanh::lean_dec(v_n_2992_);
    return v_res_2995_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(
    mut v_inst_2996_: *mut leanh::LeanObject,
    mut v_inst_2997_: *mut leanh::LeanObject,
    mut v_inst_2998_: *mut leanh::LeanObject,
    mut v_goal_2999_: *mut leanh::LeanObject,
    mut v_n_3000_: *mut leanh::LeanObject,
    mut v_k_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3004_: u8 = 0;
    v_toBind_3002_ = leanh::lean_ctor_get(v_inst_2996_, 1);
    leanh::lean_inc(v_toBind_3002_);
    v_zero_3003_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_3004_ = lean_nat_dec_eq(v_n_3000_, v_zero_3003_);
    if v_isZero_3004_ == 1 {
        let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_3002_);
        leanh::lean_dec(v_inst_2998_);
        leanh::lean_dec_ref(v_inst_2997_);
        leanh::lean_dec_ref(v_inst_2996_);
        v___x_3005_ = leanh::lean_apply_1(v_k_3001_, v_goal_2999_);
        return v___x_3005_;
    } else {
        let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3006_ = leanh::lean_box((v_isZero_3004_) as usize);
        v___f_3007_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            1,
        );
        leanh::lean_closure_set(v___f_3007_, 0, v___x_3006_);
        v_one_3008_ = leanh::lean_unsigned_to_nat(1);
        v_n_3009_ = lean_nat_sub(v_n_3000_, v_one_3008_);
        leanh::lean_inc_n(v_inst_2998_, 2);
        leanh::lean_inc_ref(v_inst_2997_);
        leanh::lean_inc_ref(v_inst_2996_);
        v___f_3010_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_3010_, 0, v_inst_2996_);
        leanh::lean_closure_set(v___f_3010_, 1, v_inst_2997_);
        leanh::lean_closure_set(v___f_3010_, 2, v_inst_2998_);
        leanh::lean_closure_set(v___f_3010_, 3, v_n_3009_);
        leanh::lean_closure_set(v___f_3010_, 4, v_k_3001_);
        v___f_3011_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__2
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_3011_, 0, v_inst_2996_);
        leanh::lean_closure_set(v___f_3011_, 1, v_inst_2997_);
        leanh::lean_closure_set(v___f_3011_, 2, v_inst_2998_);
        leanh::lean_closure_set(v___f_3011_, 3, v_goal_2999_);
        leanh::lean_closure_set(v___f_3011_, 4, v___f_3010_);
        v___x_3012_ =
            leanh::lean_apply_2(v_inst_2998_, leanh::lean_box(0), v___f_3007_);
        v___x_3013_ = leanh::lean_apply_4(
            v_toBind_3002_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3012_,
            v___f_3011_,
        );
        return v___x_3013_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___lam__1(
    mut v_inst_3014_: *mut leanh::LeanObject,
    mut v_inst_3015_: *mut leanh::LeanObject,
    mut v_inst_3016_: *mut leanh::LeanObject,
    mut v_n_3017_: *mut leanh::LeanObject,
    mut v_k_3018_: *mut leanh::LeanObject,
    mut v_g_3019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3020_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(
        v_inst_3014_,
        v_inst_3015_,
        v_inst_3016_,
        v_g_3019_,
        v_n_3017_,
        v_k_3018_,
    );
    return v___x_3020_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg___boxed(
    mut v_inst_3021_: *mut leanh::LeanObject,
    mut v_inst_3022_: *mut leanh::LeanObject,
    mut v_inst_3023_: *mut leanh::LeanObject,
    mut v_goal_3024_: *mut leanh::LeanObject,
    mut v_n_3025_: *mut leanh::LeanObject,
    mut v_k_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3027_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(
        v_inst_3021_,
        v_inst_3022_,
        v_inst_3023_,
        v_goal_3024_,
        v_n_3025_,
        v_k_3026_,
    );
    leanh::lean_dec(v_n_3025_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(
    mut v_m_3028_: *mut leanh::LeanObject,
    mut v_inst_3029_: *mut leanh::LeanObject,
    mut v_inst_3030_: *mut leanh::LeanObject,
    mut v_inst_3031_: *mut leanh::LeanObject,
    mut v_goal_3032_: *mut leanh::LeanObject,
    mut v_n_3033_: *mut leanh::LeanObject,
    mut v_k_3034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___redArg(
        v_inst_3029_,
        v_inst_3030_,
        v_inst_3031_,
        v_goal_3032_,
        v_n_3033_,
        v_k_3034_,
    );
    return v___x_3035_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN___boxed(
    mut v_m_3036_: *mut leanh::LeanObject,
    mut v_inst_3037_: *mut leanh::LeanObject,
    mut v_inst_3038_: *mut leanh::LeanObject,
    mut v_inst_3039_: *mut leanh::LeanObject,
    mut v_goal_3040_: *mut leanh::LeanObject,
    mut v_n_3041_: *mut leanh::LeanObject,
    mut v_k_3042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3043_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForallN(
        v_m_3036_,
        v_inst_3037_,
        v_inst_3038_,
        v_inst_3039_,
        v_goal_3040_,
        v_n_3041_,
        v_k_3042_,
    );
    leanh::lean_dec(v_n_3041_);
    return v_res_3043_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__10;
    v___x_3073_ = l_String_toRawSubstring_x27(v___x_3072_);
    return v___x_3073_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(
    mut v_x_3084_: *mut leanh::LeanObject,
    mut v_a_3085_: *mut leanh::LeanObject,
    mut v_a_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    v___x_3087_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__0;
    v___x_3088_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1;
    leanh::lean_inc(v_x_3084_);
    v___x_3089_ = l_Lean_Syntax_isOfKind(v_x_3084_, v___x_3088_);
    if v___x_3089_ == 0 {
        let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3084_);
        v___x_3090_ = leanh::lean_box(1);
        v___x_3091_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3091_, 0, v___x_3090_);
        leanh::lean_ctor_set(v___x_3091_, 1, v_a_3086_);
        return v___x_3091_;
    } else {
        let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3097_: u8 = 0;
        v___x_3092_ = leanh::lean_unsigned_to_nat(0);
        v___x_3093_ = leanh::lean_unsigned_to_nat(1);
        v___x_3094_ = l_Lean_Syntax_getArg(v_x_3084_, v___x_3093_);
        leanh::lean_dec(v_x_3084_);
        v___x_3095_ = leanh::lean_unsigned_to_nat(2);
        v___x_3096_ = l_Lean_Syntax_getNumArgs(v___x_3094_);
        v___x_3097_ = lean_nat_dec_le(v___x_3095_, v___x_3096_);
        if v___x_3097_ == 0 {
            let mut v___x_3098_: u8 = 0;
            leanh::lean_dec(v___x_3096_);
            leanh::lean_inc(v___x_3094_);
            v___x_3098_ = l_Lean_Syntax_matchesNull(v___x_3094_, v___x_3093_);
            if v___x_3098_ == 0 {
                let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_3094_);
                v___x_3099_ = leanh::lean_box(1);
                v___x_3100_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
                leanh::lean_ctor_set(v___x_3100_, 1, v_a_3086_);
                return v___x_3100_;
            } else {
                let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3103_: u8 = 0;
                v___x_3101_ = l_Lean_Syntax_getArg(v___x_3094_, v___x_3092_);
                leanh::lean_dec(v___x_3094_);
                v___x_3102_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3;
                leanh::lean_inc(v___x_3101_);
                v___x_3103_ = l_Lean_Syntax_isOfKind(v___x_3101_, v___x_3102_);
                if v___x_3103_ == 0 {
                    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_3101_);
                    v___x_3104_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3086_);
                    return v___x_3104_;
                } else {
                    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3107_: u8 = 0;
                    v___x_3105_ = l_Lean_Syntax_getArg(v___x_3101_, v___x_3092_);
                    leanh::lean_dec(v___x_3101_);
                    v___x_3106_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5;
                    leanh::lean_inc(v___x_3105_);
                    v___x_3107_ = l_Lean_Syntax_isOfKind(v___x_3105_, v___x_3106_);
                    if v___x_3107_ == 0 {
                        let mut v_quotContext_3108_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_currMacroScope_3109_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v_ref_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_quotContext_3108_ = leanh::lean_ctor_get(v_a_3085_, 1);
                        v_currMacroScope_3109_ = leanh::lean_ctor_get(v_a_3085_, 2);
                        v_ref_3110_ = leanh::lean_ctor_get(v_a_3085_, 5);
                        v___x_3111_ = l_Lean_SourceInfo_fromRef(v_ref_3110_, v___x_3107_);
                        v___x_3112_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7;
                        v___x_3113_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9;
                        leanh::lean_inc_n(v___x_3111_, 12);
                        v___x_3114_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3114_, 0, v___x_3111_);
                        leanh::lean_ctor_set(v___x_3114_, 1, v___x_3087_);
                        v___x_3115_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        v___x_3116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
                        v___x_3117_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12;
                        leanh::lean_inc(v_currMacroScope_3109_);
                        leanh::lean_inc(v_quotContext_3108_);
                        v___x_3118_ = l_Lean_addMacroScope(
                            v_quotContext_3108_,
                            v___x_3117_,
                            v_currMacroScope_3109_,
                        );
                        v___x_3119_ = leanh::lean_box(0);
                        v___x_3120_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        leanh::lean_ctor_set(v___x_3120_, 0, v___x_3111_);
                        leanh::lean_ctor_set(v___x_3120_, 1, v___x_3116_);
                        leanh::lean_ctor_set(v___x_3120_, 2, v___x_3118_);
                        leanh::lean_ctor_set(v___x_3120_, 3, v___x_3119_);
                        leanh::lean_inc_ref(v___x_3120_);
                        v___x_3121_ = l_Lean_Syntax_node1(v___x_3111_, v___x_3115_, v___x_3120_);
                        v___x_3122_ = l_Lean_Syntax_node1(v___x_3111_, v___x_3106_, v___x_3121_);
                        v___x_3123_ = l_Lean_Syntax_node1(v___x_3111_, v___x_3102_, v___x_3122_);
                        v___x_3124_ = l_Lean_Syntax_node1(v___x_3111_, v___x_3113_, v___x_3123_);
                        v___x_3125_ =
                            l_Lean_Syntax_node2(v___x_3111_, v___x_3088_, v___x_3114_, v___x_3124_);
                        v___x_3126_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13;
                        v___x_3127_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3127_, 0, v___x_3111_);
                        leanh::lean_ctor_set(v___x_3127_, 1, v___x_3126_);
                        v___x_3128_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14;
                        v___x_3129_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15;
                        v___x_3130_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3130_, 0, v___x_3111_);
                        leanh::lean_ctor_set(v___x_3130_, 1, v___x_3128_);
                        v___x_3131_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16;
                        v___x_3132_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3132_, 0, v___x_3111_);
                        leanh::lean_ctor_set(v___x_3132_, 1, v___x_3131_);
                        v___x_3133_ = l_Lean_Syntax_node4(
                            v___x_3111_,
                            v___x_3129_,
                            v___x_3130_,
                            v___x_3120_,
                            v___x_3132_,
                            v___x_3105_,
                        );
                        v___x_3134_ = l_Lean_Syntax_node3(
                            v___x_3111_,
                            v___x_3113_,
                            v___x_3125_,
                            v___x_3127_,
                            v___x_3133_,
                        );
                        v___x_3135_ = l_Lean_Syntax_node1(v___x_3111_, v___x_3112_, v___x_3134_);
                        v___x_3136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3136_, 0, v___x_3135_);
                        leanh::lean_ctor_set(v___x_3136_, 1, v_a_3086_);
                        return v___x_3136_;
                    } else {
                        let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3139_: u8 = 0;
                        v___x_3137_ = l_Lean_Syntax_getArg(v___x_3105_, v___x_3092_);
                        v___x_3138_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        v___x_3139_ = l_Lean_Syntax_isOfKind(v___x_3137_, v___x_3138_);
                        if v___x_3139_ == 0 {
                            let mut v_quotContext_3140_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_currMacroScope_3141_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_ref_3142_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3143_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3144_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3145_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3146_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3147_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3148_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3149_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3150_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3151_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3152_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3153_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3154_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3155_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3156_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3157_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3158_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3159_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3160_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3161_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3162_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3163_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3164_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3165_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3166_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3167_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v_quotContext_3140_ = leanh::lean_ctor_get(v_a_3085_, 1);
                            v_currMacroScope_3141_ = leanh::lean_ctor_get(v_a_3085_, 2);
                            v_ref_3142_ = leanh::lean_ctor_get(v_a_3085_, 5);
                            v___x_3143_ = l_Lean_SourceInfo_fromRef(v_ref_3142_, v___x_3139_);
                            v___x_3144_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7;
                            v___x_3145_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9;
                            leanh::lean_inc_n(v___x_3143_, 12);
                            v___x_3146_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3146_, 0, v___x_3143_);
                            leanh::lean_ctor_set(v___x_3146_, 1, v___x_3087_);
                            v___x_3147_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11_once), _init_l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__11);
                            v___x_3148_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__12;
                            leanh::lean_inc(v_currMacroScope_3141_);
                            leanh::lean_inc(v_quotContext_3140_);
                            v___x_3149_ = l_Lean_addMacroScope(
                                v_quotContext_3140_,
                                v___x_3148_,
                                v_currMacroScope_3141_,
                            );
                            v___x_3150_ = leanh::lean_box(0);
                            v___x_3151_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3151_, 0, v___x_3143_);
                            leanh::lean_ctor_set(v___x_3151_, 1, v___x_3147_);
                            leanh::lean_ctor_set(v___x_3151_, 2, v___x_3149_);
                            leanh::lean_ctor_set(v___x_3151_, 3, v___x_3150_);
                            leanh::lean_inc_ref(v___x_3151_);
                            v___x_3152_ =
                                l_Lean_Syntax_node1(v___x_3143_, v___x_3138_, v___x_3151_);
                            v___x_3153_ =
                                l_Lean_Syntax_node1(v___x_3143_, v___x_3106_, v___x_3152_);
                            v___x_3154_ =
                                l_Lean_Syntax_node1(v___x_3143_, v___x_3102_, v___x_3153_);
                            v___x_3155_ =
                                l_Lean_Syntax_node1(v___x_3143_, v___x_3145_, v___x_3154_);
                            v___x_3156_ = l_Lean_Syntax_node2(
                                v___x_3143_,
                                v___x_3088_,
                                v___x_3146_,
                                v___x_3155_,
                            );
                            v___x_3157_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13;
                            v___x_3158_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3158_, 0, v___x_3143_);
                            leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                            v___x_3159_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__14;
                            v___x_3160_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__15;
                            v___x_3161_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3161_, 0, v___x_3143_);
                            leanh::lean_ctor_set(v___x_3161_, 1, v___x_3159_);
                            v___x_3162_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__16;
                            v___x_3163_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3163_, 0, v___x_3143_);
                            leanh::lean_ctor_set(v___x_3163_, 1, v___x_3162_);
                            v___x_3164_ = l_Lean_Syntax_node4(
                                v___x_3143_,
                                v___x_3160_,
                                v___x_3161_,
                                v___x_3151_,
                                v___x_3163_,
                                v___x_3105_,
                            );
                            v___x_3165_ = l_Lean_Syntax_node3(
                                v___x_3143_,
                                v___x_3145_,
                                v___x_3156_,
                                v___x_3158_,
                                v___x_3164_,
                            );
                            v___x_3166_ =
                                l_Lean_Syntax_node1(v___x_3143_, v___x_3144_, v___x_3165_);
                            v___x_3167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3167_, 0, v___x_3166_);
                            leanh::lean_ctor_set(v___x_3167_, 1, v_a_3086_);
                            return v___x_3167_;
                        } else {
                            let mut v___x_3168_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_3105_);
                            v___x_3168_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3086_);
                            return v___x_3168_;
                        }
                    }
                }
            }
        } else {
            let mut v_ref_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_pats_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3178_: u8 = 0;
            let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ref_3169_ = leanh::lean_ctor_get(v_a_3085_, 5);
            v___x_3170_ = l_Lean_Syntax_getArg(v___x_3094_, v___x_3092_);
            v___x_3171_ = l_Lean_Syntax_getArg(v___x_3094_, v___x_3093_);
            v___x_3172_ = l_Lean_Syntax_getArgs(v___x_3094_);
            leanh::lean_dec(v___x_3094_);
            v___x_3173_ = l_Array_extract___redArg(v___x_3172_, v___x_3095_, v___x_3096_);
            leanh::lean_dec_ref(v___x_3172_);
            v___x_3174_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__9;
            v___x_3175_ = leanh::lean_box(2);
            v___x_3176_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_3176_, 0, v___x_3175_);
            leanh::lean_ctor_set(v___x_3176_, 1, v___x_3174_);
            leanh::lean_ctor_set(v___x_3176_, 2, v___x_3173_);
            v_pats_3177_ = l_Lean_Syntax_getArgs(v___x_3176_);
            leanh::lean_dec_ref_known(v___x_3176_, 3);
            v___x_3178_ = 0;
            v___x_3179_ = l_Lean_SourceInfo_fromRef(v_ref_3169_, v___x_3178_);
            v___x_3180_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__7;
            leanh::lean_inc_n(v___x_3179_, 7);
            v___x_3181_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3181_, 0, v___x_3179_);
            leanh::lean_ctor_set(v___x_3181_, 1, v___x_3087_);
            v___x_3182_ = l_Lean_Syntax_node1(v___x_3179_, v___x_3174_, v___x_3170_);
            leanh::lean_inc_ref(v___x_3181_);
            v___x_3183_ = l_Lean_Syntax_node2(v___x_3179_, v___x_3088_, v___x_3181_, v___x_3182_);
            v___x_3184_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__13;
            v___x_3185_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3185_, 0, v___x_3179_);
            leanh::lean_ctor_set(v___x_3185_, 1, v___x_3184_);
            v___x_3186_ = l_Array_mkArray1___redArg(v___x_3171_);
            v___x_3187_ = l_Array_append___redArg(v___x_3186_, v_pats_3177_);
            leanh::lean_dec_ref(v_pats_3177_);
            v___x_3188_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_3188_, 0, v___x_3179_);
            leanh::lean_ctor_set(v___x_3188_, 1, v___x_3174_);
            leanh::lean_ctor_set(v___x_3188_, 2, v___x_3187_);
            v___x_3189_ = l_Lean_Syntax_node2(v___x_3179_, v___x_3088_, v___x_3181_, v___x_3188_);
            v___x_3190_ = l_Lean_Syntax_node3(
                v___x_3179_,
                v___x_3174_,
                v___x_3183_,
                v___x_3185_,
                v___x_3189_,
            );
            v___x_3191_ = l_Lean_Syntax_node1(v___x_3179_, v___x_3180_, v___x_3190_);
            v___x_3192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3192_, 0, v___x_3191_);
            leanh::lean_ctor_set(v___x_3192_, 1, v_a_3086_);
            return v___x_3192_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___boxed(
    mut v_x_3193_: *mut leanh::LeanObject,
    mut v_a_3194_: *mut leanh::LeanObject,
    mut v_a_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1(v_x_3193_, v_a_3194_, v_a_3195_);
    leanh::lean_dec_ref(v_a_3194_);
    return v_res_3196_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ = leanh::lean_box(0);
    v___x_3198_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3199_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3199_, 0, v___x_3198_);
    leanh::lean_ctor_set(v___x_3199_, 1, v___x_3197_);
    return v___x_3199_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___closed__0);
    v___x_3202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3202_, 0, v___x_3201_);
    return v___x_3202_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg___boxed(
    mut v___y_3203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
    return v_res_3204_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(
    mut v_00_u03b1_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
    mut v___y_3209_: *mut leanh::LeanObject,
    mut v___y_3210_: *mut leanh::LeanObject,
    mut v___y_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
    return v___x_3215_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___boxed(
    mut v_00_u03b1_3216_: *mut leanh::LeanObject,
    mut v___y_3217_: *mut leanh::LeanObject,
    mut v___y_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
    mut v___y_3222_: *mut leanh::LeanObject,
    mut v___y_3223_: *mut leanh::LeanObject,
    mut v___y_3224_: *mut leanh::LeanObject,
    mut v___y_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0(v_00_u03b1_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
    leanh::lean_dec(v___y_3224_);
    leanh::lean_dec_ref(v___y_3223_);
    leanh::lean_dec(v___y_3222_);
    leanh::lean_dec_ref(v___y_3221_);
    leanh::lean_dec(v___y_3220_);
    leanh::lean_dec_ref(v___y_3219_);
    leanh::lean_dec(v___y_3218_);
    leanh::lean_dec_ref(v___y_3217_);
    return v_res_3226_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(
    mut v_x_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
    mut v___y_3230_: *mut leanh::LeanObject,
    mut v___y_3231_: *mut leanh::LeanObject,
    mut v___y_3232_: *mut leanh::LeanObject,
    mut v___y_3233_: *mut leanh::LeanObject,
    mut v___y_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3231_);
    leanh::lean_inc_ref(v___y_3230_);
    leanh::lean_inc(v___y_3229_);
    leanh::lean_inc_ref(v___y_3228_);
    v___x_3237_ = leanh::lean_apply_9(
        v_x_3227_,
        v___y_3228_,
        v___y_3229_,
        v___y_3230_,
        v___y_3231_,
        v___y_3232_,
        v___y_3233_,
        v___y_3234_,
        v___y_3235_,
        leanh::lean_box(0),
    );
    return v___x_3237_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed(
    mut v_x_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
    mut v___y_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
    mut v___y_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0(v_x_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
    leanh::lean_dec(v___y_3242_);
    leanh::lean_dec_ref(v___y_3241_);
    leanh::lean_dec(v___y_3240_);
    leanh::lean_dec_ref(v___y_3239_);
    return v_res_3248_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(
    mut v_mvarId_3249_: *mut leanh::LeanObject,
    mut v_x_3250_: *mut leanh::LeanObject,
    mut v___y_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3254_);
                leanh::lean_inc_ref(v___y_3253_);
                leanh::lean_inc(v___y_3252_);
                leanh::lean_inc_ref(v___y_3251_);
                v___f_3260_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_3260_, 0, v_x_3250_);
                leanh::lean_closure_set(v___f_3260_, 1, v___y_3251_);
                leanh::lean_closure_set(v___f_3260_, 2, v___y_3252_);
                leanh::lean_closure_set(v___f_3260_, 3, v___y_3253_);
                leanh::lean_closure_set(v___f_3260_, 4, v___y_3254_);
                v___x_3261_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3249_,
                    v___f_3260_,
                    v___y_3255_,
                    v___y_3256_,
                    v___y_3257_,
                    v___y_3258_,
                );
                if leanh::lean_obj_tag(v___x_3261_) == 0 {
                    return v___x_3261_;
                } else {
                    v_a_3262_ = leanh::lean_ctor_get(v___x_3261_, 0);
                    v_isSharedCheck_3269_ = (!leanh::lean_is_exclusive(v___x_3261_)) as u8;
                    if v_isSharedCheck_3269_ == 0 {
                        v___x_3264_ = v___x_3261_;
                        v_isShared_3265_ = v_isSharedCheck_3269_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3262_);
                        leanh::lean_dec(v___x_3261_);
                        v___x_3264_ = leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3269_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3265_ == 0 {
                    v___x_3267_ = v___x_3264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
                    v___x_3267_ = v_reuseFailAlloc_3268_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg___boxed(
    mut v_mvarId_3270_: *mut leanh::LeanObject,
    mut v_x_3271_: *mut leanh::LeanObject,
    mut v___y_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
    mut v___y_3278_: *mut leanh::LeanObject,
    mut v___y_3279_: *mut leanh::LeanObject,
    mut v___y_3280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3281_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_3270_, v_x_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
    leanh::lean_dec(v___y_3279_);
    leanh::lean_dec_ref(v___y_3278_);
    leanh::lean_dec(v___y_3277_);
    leanh::lean_dec_ref(v___y_3276_);
    leanh::lean_dec(v___y_3275_);
    leanh::lean_dec_ref(v___y_3274_);
    leanh::lean_dec(v___y_3273_);
    leanh::lean_dec_ref(v___y_3272_);
    return v_res_3281_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(
    mut v_00_u03b1_3282_: *mut leanh::LeanObject,
    mut v_mvarId_3283_: *mut leanh::LeanObject,
    mut v_x_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
    mut v___y_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3294_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_mvarId_3283_, v_x_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
    return v___x_3294_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___boxed(
    mut v_00_u03b1_3295_: *mut leanh::LeanObject,
    mut v_mvarId_3296_: *mut leanh::LeanObject,
    mut v_x_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
    mut v___y_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3(
            v_00_u03b1_3295_,
            v_mvarId_3296_,
            v_x_3297_,
            v___y_3298_,
            v___y_3299_,
            v___y_3300_,
            v___y_3301_,
            v___y_3302_,
            v___y_3303_,
            v___y_3304_,
            v___y_3305_,
        );
    leanh::lean_dec(v___y_3305_);
    leanh::lean_dec_ref(v___y_3304_);
    leanh::lean_dec(v___y_3303_);
    leanh::lean_dec_ref(v___y_3302_);
    leanh::lean_dec(v___y_3301_);
    leanh::lean_dec_ref(v___y_3300_);
    leanh::lean_dec(v___y_3299_);
    leanh::lean_dec_ref(v___y_3298_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(
    mut v_val_3308_: *mut leanh::LeanObject,
    mut v_newGoal_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
    mut v___y_3315_: *mut leanh::LeanObject,
    mut v___y_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3319_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_newGoal_3309_);
                v___x_3320_ = leanh::lean_box(0);
                v___x_3321_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3319_,
                    v___x_3320_,
                    v___y_3314_,
                    v___y_3315_,
                    v___y_3316_,
                    v___y_3317_,
                );
                if leanh::lean_obj_tag(v___x_3321_) == 0 {
                    v_a_3322_ = leanh::lean_ctor_get(v___x_3321_, 0);
                    v_isSharedCheck_3333_ = (!leanh::lean_is_exclusive(v___x_3321_)) as u8;
                    if v_isSharedCheck_3333_ == 0 {
                        v___x_3324_ = v___x_3321_;
                        v_isShared_3325_ = v_isSharedCheck_3333_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3322_);
                        leanh::lean_dec(v___x_3321_);
                        v___x_3324_ = leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3333_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3321_;
                }
            }
            1 => {
                v___x_3326_ = lean_st_ref_take(v_val_3308_);
                v___x_3327_ = l_Lean_Expr_mvarId_x21(v_a_3322_);
                v___x_3328_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3328_, 0, v___x_3327_);
                leanh::lean_ctor_set(v___x_3328_, 1, v___x_3326_);
                v___x_3329_ = lean_st_ref_set(v_val_3308_, v___x_3328_);
                if v_isShared_3325_ == 0 {
                    v___x_3331_ = v___x_3324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3322_);
                    v___x_3331_ = v_reuseFailAlloc_3332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed(
    mut v_val_3334_: *mut leanh::LeanObject,
    mut v_newGoal_3335_: *mut leanh::LeanObject,
    mut v___y_3336_: *mut leanh::LeanObject,
    mut v___y_3337_: *mut leanh::LeanObject,
    mut v___y_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3345_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0(
        v_val_3334_,
        v_newGoal_3335_,
        v___y_3336_,
        v___y_3337_,
        v___y_3338_,
        v___y_3339_,
        v___y_3340_,
        v___y_3341_,
        v___y_3342_,
        v___y_3343_,
    );
    leanh::lean_dec(v___y_3343_);
    leanh::lean_dec_ref(v___y_3342_);
    leanh::lean_dec(v___y_3341_);
    leanh::lean_dec_ref(v___y_3340_);
    leanh::lean_dec(v___y_3339_);
    leanh::lean_dec_ref(v___y_3338_);
    leanh::lean_dec(v___y_3337_);
    leanh::lean_dec_ref(v___y_3336_);
    leanh::lean_dec(v_val_3334_);
    return v_res_3345_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(
    mut v_x_3346_: *mut leanh::LeanObject,
    mut v_x_3347_: *mut leanh::LeanObject,
    mut v_x_3348_: *mut leanh::LeanObject,
    mut v_x_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3350_ = leanh::lean_ctor_get(v_x_3346_, 0);
                v_vs_3351_ = leanh::lean_ctor_get(v_x_3346_, 1);
                v_isSharedCheck_3375_ = (!leanh::lean_is_exclusive(v_x_3346_)) as u8;
                if v_isSharedCheck_3375_ == 0 {
                    v___x_3353_ = v_x_3346_;
                    v_isShared_3354_ = v_isSharedCheck_3375_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3351_);
                    leanh::lean_inc(v_ks_3350_);
                    leanh::lean_dec(v_x_3346_);
                    v___x_3353_ = leanh::lean_box(0);
                    v_isShared_3354_ = v_isSharedCheck_3375_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3355_ = lean_array_get_size(v_ks_3350_);
                v___x_3356_ = lean_nat_dec_lt(v_x_3347_, v___x_3355_);
                if v___x_3356_ == 0 {
                    leanh::lean_dec(v_x_3347_);
                    v___x_3357_ = lean_array_push(v_ks_3350_, v_x_3348_);
                    v___x_3358_ = lean_array_push(v_vs_3351_, v_x_3349_);
                    if v_isShared_3354_ == 0 {
                        leanh::lean_ctor_set(v___x_3353_, 1, v___x_3358_);
                        leanh::lean_ctor_set(v___x_3353_, 0, v___x_3357_);
                        v___x_3360_ = v___x_3353_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3361_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3357_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3358_);
                        v___x_3360_ = v_reuseFailAlloc_3361_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3362_ = lean_array_fget_borrowed(v_ks_3350_, v_x_3347_);
                    v___x_3363_ = l_Lean_instBEqMVarId_beq(v_x_3348_, v_k_x27_3362_);
                    if v___x_3363_ == 0 {
                        if v_isShared_3354_ == 0 {
                            v___x_3365_ = v___x_3353_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3369_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_ks_3350_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_vs_3351_);
                            v___x_3365_ = v_reuseFailAlloc_3369_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3370_ = lean_array_fset(v_ks_3350_, v_x_3347_, v_x_3348_);
                        v___x_3371_ = lean_array_fset(v_vs_3351_, v_x_3347_, v_x_3349_);
                        leanh::lean_dec(v_x_3347_);
                        if v_isShared_3354_ == 0 {
                            leanh::lean_ctor_set(v___x_3353_, 1, v___x_3371_);
                            leanh::lean_ctor_set(v___x_3353_, 0, v___x_3370_);
                            v___x_3373_ = v___x_3353_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3374_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3370_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3371_);
                            v___x_3373_ = v_reuseFailAlloc_3374_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3360_;
            }
            3 => {
                v___x_3366_ = leanh::lean_unsigned_to_nat(1);
                v___x_3367_ = lean_nat_add(v_x_3347_, v___x_3366_);
                leanh::lean_dec(v_x_3347_);
                v_x_3346_ = v___x_3365_;
                v_x_3347_ = v___x_3367_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(
    mut v_n_3376_: *mut leanh::LeanObject,
    mut v_k_3377_: *mut leanh::LeanObject,
    mut v_v_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = leanh::lean_unsigned_to_nat(0);
    v___x_3380_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_n_3376_, v___x_3379_, v_k_3377_, v_v_3378_);
    return v___x_3380_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_3381_: usize = 0;
    let mut v___x_3382_: usize = 0;
    let mut v___x_3383_: usize = 0;
    v___x_3381_ = 5usize;
    v___x_3382_ = 1usize;
    v___x_3383_ = lean_usize_shift_left(v___x_3382_, v___x_3381_);
    return v___x_3383_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_3384_: usize = 0;
    let mut v___x_3385_: usize = 0;
    let mut v___x_3386_: usize = 0;
    v___x_3384_ = 1usize;
    v___x_3385_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__0);
    v___x_3386_ = lean_usize_sub(v___x_3385_, v___x_3384_);
    return v___x_3386_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3387_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(
    mut v_x_3388_: *mut leanh::LeanObject,
    mut v_x_3389_: usize,
    mut v_x_3390_: usize,
    mut v_x_3391_: *mut leanh::LeanObject,
    mut v_x_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: usize = 0;
    let mut v___x_3395_: usize = 0;
    let mut v___x_3396_: usize = 0;
    let mut v___x_3397_: usize = 0;
    let mut v_j_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v_v_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3418_: u8 = 0;
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_node_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3429_: usize = 0;
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3435_: u8 = 0;
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_unused_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: u8 = 0;
    let mut v_ks_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: usize = 0;
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v_reuseFailAlloc_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3388_) == 0 {
                    v_es_3393_ = leanh::lean_ctor_get(v_x_3388_, 0);
                    v___x_3394_ = 5usize;
                    v___x_3395_ = 1usize;
                    v___x_3396_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__1);
                    v___x_3397_ = lean_usize_land(v_x_3389_, v___x_3396_);
                    v_j_3398_ = lean_usize_to_nat(v___x_3397_);
                    v___x_3399_ = lean_array_get_size(v_es_3393_);
                    v___x_3400_ = lean_nat_dec_lt(v_j_3398_, v___x_3399_);
                    if v___x_3400_ == 0 {
                        leanh::lean_dec(v_j_3398_);
                        leanh::lean_dec(v_x_3392_);
                        leanh::lean_dec(v_x_3391_);
                        return v_x_3388_;
                    } else {
                        leanh::lean_inc_ref(v_es_3393_);
                        v_isSharedCheck_3437_ = (!leanh::lean_is_exclusive(v_x_3388_)) as u8;
                        if v_isSharedCheck_3437_ == 0 {
                            v_unused_3438_ = leanh::lean_ctor_get(v_x_3388_, 0);
                            leanh::lean_dec(v_unused_3438_);
                            v___x_3402_ = v_x_3388_;
                            v_isShared_3403_ = v_isSharedCheck_3437_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3388_);
                            v___x_3402_ = leanh::lean_box(0);
                            v_isShared_3403_ = v_isSharedCheck_3437_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3439_ = leanh::lean_ctor_get(v_x_3388_, 0);
                    v_vs_3440_ = leanh::lean_ctor_get(v_x_3388_, 1);
                    v_isSharedCheck_3460_ = (!leanh::lean_is_exclusive(v_x_3388_)) as u8;
                    if v_isSharedCheck_3460_ == 0 {
                        v___x_3442_ = v_x_3388_;
                        v_isShared_3443_ = v_isSharedCheck_3460_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3440_);
                        leanh::lean_inc(v_ks_3439_);
                        leanh::lean_dec(v_x_3388_);
                        v___x_3442_ = leanh::lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3460_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3404_ = lean_array_fget(v_es_3393_, v_j_3398_);
                v___x_3405_ = leanh::lean_box(0);
                v_xs_x27_3406_ = lean_array_fset(v_es_3393_, v_j_3398_, v___x_3405_);
                match leanh::lean_obj_tag(v_v_3404_) {
                    0 => {
                        v_key_3413_ = leanh::lean_ctor_get(v_v_3404_, 0);
                        v_val_3414_ = leanh::lean_ctor_get(v_v_3404_, 1);
                        v_isSharedCheck_3424_ = (!leanh::lean_is_exclusive(v_v_3404_)) as u8;
                        if v_isSharedCheck_3424_ == 0 {
                            v___x_3416_ = v_v_3404_;
                            v_isShared_3417_ = v_isSharedCheck_3424_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3414_);
                            leanh::lean_inc(v_key_3413_);
                            leanh::lean_dec(v_v_3404_);
                            v___x_3416_ = leanh::lean_box(0);
                            v_isShared_3417_ = v_isSharedCheck_3424_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3425_ = leanh::lean_ctor_get(v_v_3404_, 0);
                        v_isSharedCheck_3435_ = (!leanh::lean_is_exclusive(v_v_3404_)) as u8;
                        if v_isSharedCheck_3435_ == 0 {
                            v___x_3427_ = v_v_3404_;
                            v_isShared_3428_ = v_isSharedCheck_3435_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3425_);
                            leanh::lean_dec(v_v_3404_);
                            v___x_3427_ = leanh::lean_box(0);
                            v_isShared_3428_ = v_isSharedCheck_3435_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3436_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3436_, 0, v_x_3391_);
                        leanh::lean_ctor_set(v___x_3436_, 1, v_x_3392_);
                        v___y_3408_ = v___x_3436_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3409_ = lean_array_fset(v_xs_x27_3406_, v_j_3398_, v___y_3408_);
                leanh::lean_dec(v_j_3398_);
                if v_isShared_3403_ == 0 {
                    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3409_);
                    v___x_3411_ = v___x_3402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3411_;
            }
            4 => {
                v___x_3418_ = l_Lean_instBEqMVarId_beq(v_x_3391_, v_key_3413_);
                if v___x_3418_ == 0 {
                    leanh::lean_del_object(v___x_3416_);
                    v___x_3419_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3413_,
                        v_val_3414_,
                        v_x_3391_,
                        v_x_3392_,
                    );
                    v___x_3420_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3420_, 0, v___x_3419_);
                    v___y_3408_ = v___x_3420_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3414_);
                    leanh::lean_dec(v_key_3413_);
                    if v_isShared_3417_ == 0 {
                        leanh::lean_ctor_set(v___x_3416_, 1, v_x_3392_);
                        leanh::lean_ctor_set(v___x_3416_, 0, v_x_3391_);
                        v___x_3422_ = v___x_3416_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3423_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_x_3391_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_x_3392_);
                        v___x_3422_ = v_reuseFailAlloc_3423_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3408_ = v___x_3422_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3429_ = lean_usize_shift_right(v_x_3389_, v___x_3394_);
                v___x_3430_ = lean_usize_add(v_x_3390_, v___x_3395_);
                v___x_3431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_node_3425_, v___x_3429_, v___x_3430_, v_x_3391_, v_x_3392_);
                if v_isShared_3428_ == 0 {
                    leanh::lean_ctor_set(v___x_3427_, 0, v___x_3431_);
                    v___x_3433_ = v___x_3427_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
                    v___x_3433_ = v_reuseFailAlloc_3434_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3408_ = v___x_3433_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3443_ == 0 {
                    v___x_3445_ = v___x_3442_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3459_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_ks_3439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_vs_3440_);
                    v___x_3445_ = v_reuseFailAlloc_3459_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3446_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v___x_3445_, v_x_3391_, v_x_3392_);
                v___x_3454_ = 7usize;
                v___x_3455_ = lean_usize_dec_le(v___x_3454_, v_x_3390_);
                if v___x_3455_ == 0 {
                    v___x_3456_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3446_);
                    v___x_3457_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3458_ = lean_nat_dec_lt(v___x_3456_, v___x_3457_);
                    leanh::lean_dec(v___x_3456_);
                    v___y_3448_ = v___x_3458_;
                    state = 10;
                    continue;
                } else {
                    v___y_3448_ = v___x_3455_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3448_ == 0 {
                    v_ks_3449_ = leanh::lean_ctor_get(v_newNode_3446_, 0);
                    leanh::lean_inc_ref(v_ks_3449_);
                    v_vs_3450_ = leanh::lean_ctor_get(v_newNode_3446_, 1);
                    leanh::lean_inc_ref(v_vs_3450_);
                    leanh::lean_dec_ref(v_newNode_3446_);
                    v___x_3451_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3452_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___closed__2);
                    v___x_3453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_x_3390_, v_ks_3449_, v_vs_3450_, v___x_3451_, v___x_3452_);
                    leanh::lean_dec_ref(v_vs_3450_);
                    leanh::lean_dec_ref(v_ks_3449_);
                    return v___x_3453_;
                } else {
                    return v_newNode_3446_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(
    mut v_depth_3461_: usize,
    mut v_keys_3462_: *mut leanh::LeanObject,
    mut v_vals_3463_: *mut leanh::LeanObject,
    mut v_i_3464_: *mut leanh::LeanObject,
    mut v_entries_3465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: u8 = 0;
    let mut v_k_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u64 = 0;
    let mut v_h_3471_: usize = 0;
    let mut v___x_3472_: usize = 0;
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: usize = 0;
    let mut v___x_3475_: usize = 0;
    let mut v___x_3476_: usize = 0;
    let mut v_h_3477_: usize = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3466_ = lean_array_get_size(v_keys_3462_);
                v___x_3467_ = lean_nat_dec_lt(v_i_3464_, v___x_3466_);
                if v___x_3467_ == 0 {
                    leanh::lean_dec(v_i_3464_);
                    return v_entries_3465_;
                } else {
                    v_k_3468_ = lean_array_fget_borrowed(v_keys_3462_, v_i_3464_);
                    v_v_3469_ = lean_array_fget_borrowed(v_vals_3463_, v_i_3464_);
                    v___x_3470_ = l_Lean_instHashableMVarId_hash(v_k_3468_);
                    v_h_3471_ = lean_uint64_to_usize(v___x_3470_);
                    v___x_3472_ = 5usize;
                    v___x_3473_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3474_ = 1usize;
                    v___x_3475_ = lean_usize_sub(v_depth_3461_, v___x_3474_);
                    v___x_3476_ = lean_usize_mul(v___x_3472_, v___x_3475_);
                    v_h_3477_ = lean_usize_shift_right(v_h_3471_, v___x_3476_);
                    v___x_3478_ = lean_nat_add(v_i_3464_, v___x_3473_);
                    leanh::lean_dec(v_i_3464_);
                    leanh::lean_inc(v_v_3469_);
                    leanh::lean_inc(v_k_3468_);
                    v___x_3479_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_entries_3465_, v_h_3477_, v_depth_3461_, v_k_3468_, v_v_3469_);
                    v_i_3464_ = v___x_3478_;
                    v_entries_3465_ = v___x_3479_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg___boxed(
    mut v_depth_3481_: *mut leanh::LeanObject,
    mut v_keys_3482_: *mut leanh::LeanObject,
    mut v_vals_3483_: *mut leanh::LeanObject,
    mut v_i_3484_: *mut leanh::LeanObject,
    mut v_entries_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3486_: usize = 0;
    let mut v_res_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3486_ = leanh::lean_unbox_usize(v_depth_3481_);
    leanh::lean_dec(v_depth_3481_);
    v_res_3487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_boxed_3486_, v_keys_3482_, v_vals_3483_, v_i_3484_, v_entries_3485_);
    leanh::lean_dec_ref(v_vals_3483_);
    leanh::lean_dec_ref(v_keys_3482_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_x_3488_: *mut leanh::LeanObject,
    mut v_x_3489_: *mut leanh::LeanObject,
    mut v_x_3490_: *mut leanh::LeanObject,
    mut v_x_3491_: *mut leanh::LeanObject,
    mut v_x_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_20313__boxed_3493_: usize = 0;
    let mut v_x_20314__boxed_3494_: usize = 0;
    let mut v_res_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_20313__boxed_3493_ = leanh::lean_unbox_usize(v_x_3489_);
    leanh::lean_dec(v_x_3489_);
    v_x_20314__boxed_3494_ = leanh::lean_unbox_usize(v_x_3490_);
    leanh::lean_dec(v_x_3490_);
    v_res_3495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_3488_, v_x_20313__boxed_3493_, v_x_20314__boxed_3494_, v_x_3491_, v_x_3492_);
    return v_res_3495_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(
    mut v_x_3496_: *mut leanh::LeanObject,
    mut v_x_3497_: *mut leanh::LeanObject,
    mut v_x_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3499_: u64 = 0;
    let mut v___x_3500_: usize = 0;
    let mut v___x_3501_: usize = 0;
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3499_ = l_Lean_instHashableMVarId_hash(v_x_3497_);
    v___x_3500_ = lean_uint64_to_usize(v___x_3499_);
    v___x_3501_ = 1usize;
    v___x_3502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_3496_, v___x_3500_, v___x_3501_, v_x_3497_, v_x_3498_);
    return v___x_3502_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(
    mut v_mvarId_3503_: *mut leanh::LeanObject,
    mut v_val_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v_depth_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3507_ = lean_st_ref_take(v___y_3505_);
                v_mctx_3508_ = leanh::lean_ctor_get(v___x_3507_, 0);
                v_cache_3509_ = leanh::lean_ctor_get(v___x_3507_, 1);
                v_zetaDeltaFVarIds_3510_ = leanh::lean_ctor_get(v___x_3507_, 2);
                v_postponed_3511_ = leanh::lean_ctor_get(v___x_3507_, 3);
                v_diag_3512_ = leanh::lean_ctor_get(v___x_3507_, 4);
                v_isSharedCheck_3540_ = (!leanh::lean_is_exclusive(v___x_3507_)) as u8;
                if v_isSharedCheck_3540_ == 0 {
                    v___x_3514_ = v___x_3507_;
                    v_isShared_3515_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3512_);
                    leanh::lean_inc(v_postponed_3511_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3510_);
                    leanh::lean_inc(v_cache_3509_);
                    leanh::lean_inc(v_mctx_3508_);
                    leanh::lean_dec(v___x_3507_);
                    v___x_3514_ = leanh::lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3516_ = leanh::lean_ctor_get(v_mctx_3508_, 0);
                v_levelAssignDepth_3517_ = leanh::lean_ctor_get(v_mctx_3508_, 1);
                v_lmvarCounter_3518_ = leanh::lean_ctor_get(v_mctx_3508_, 2);
                v_mvarCounter_3519_ = leanh::lean_ctor_get(v_mctx_3508_, 3);
                v_lDecls_3520_ = leanh::lean_ctor_get(v_mctx_3508_, 4);
                v_decls_3521_ = leanh::lean_ctor_get(v_mctx_3508_, 5);
                v_userNames_3522_ = leanh::lean_ctor_get(v_mctx_3508_, 6);
                v_lAssignment_3523_ = leanh::lean_ctor_get(v_mctx_3508_, 7);
                v_eAssignment_3524_ = leanh::lean_ctor_get(v_mctx_3508_, 8);
                v_dAssignment_3525_ = leanh::lean_ctor_get(v_mctx_3508_, 9);
                v_isSharedCheck_3539_ = (!leanh::lean_is_exclusive(v_mctx_3508_)) as u8;
                if v_isSharedCheck_3539_ == 0 {
                    v___x_3527_ = v_mctx_3508_;
                    v_isShared_3528_ = v_isSharedCheck_3539_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3525_);
                    leanh::lean_inc(v_eAssignment_3524_);
                    leanh::lean_inc(v_lAssignment_3523_);
                    leanh::lean_inc(v_userNames_3522_);
                    leanh::lean_inc(v_decls_3521_);
                    leanh::lean_inc(v_lDecls_3520_);
                    leanh::lean_inc(v_mvarCounter_3519_);
                    leanh::lean_inc(v_lmvarCounter_3518_);
                    leanh::lean_inc(v_levelAssignDepth_3517_);
                    leanh::lean_inc(v_depth_3516_);
                    leanh::lean_dec(v_mctx_3508_);
                    v___x_3527_ = leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3529_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_eAssignment_3524_, v_mvarId_3503_, v_val_3504_);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set(v___x_3527_, 8, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_depth_3516_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3538_,
                        1,
                        v_levelAssignDepth_3517_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_lmvarCounter_3518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_mvarCounter_3519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_lDecls_3520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 5, v_decls_3521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 6, v_userNames_3522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 7, v_lAssignment_3523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 8, v___x_3529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 9, v_dAssignment_3525_);
                    v___x_3531_ = v_reuseFailAlloc_3538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3515_ == 0 {
                    leanh::lean_ctor_set(v___x_3514_, 0, v___x_3531_);
                    v___x_3533_ = v___x_3514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3537_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_cache_3509_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3537_,
                        2,
                        v_zetaDeltaFVarIds_3510_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_postponed_3511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_diag_3512_);
                    v___x_3533_ = v_reuseFailAlloc_3537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3534_ = lean_st_ref_set(v___y_3505_, v___x_3533_);
                v___x_3535_ = leanh::lean_box(0);
                v___x_3536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3536_, 0, v___x_3535_);
                return v___x_3536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg___boxed(
    mut v_mvarId_3541_: *mut leanh::LeanObject,
    mut v_val_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(
            v_mvarId_3541_,
            v_val_3542_,
            v___y_3543_,
        );
    leanh::lean_dec(v___y_3543_);
    return v_res_3545_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(
    mut v_k_3546_: *mut leanh::LeanObject,
    mut v_b_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3551_);
    leanh::lean_inc_ref(v___y_3550_);
    leanh::lean_inc(v___y_3549_);
    leanh::lean_inc_ref(v___y_3548_);
    v___x_3553_ = leanh::lean_apply_6(
        v_k_3546_,
        v_b_3547_,
        v___y_3548_,
        v___y_3549_,
        v___y_3550_,
        v___y_3551_,
        leanh::lean_box(0),
    );
    return v___x_3553_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed(
    mut v_k_3554_: *mut leanh::LeanObject,
    mut v_b_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0(v_k_3554_, v_b_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
    leanh::lean_dec(v___y_3559_);
    leanh::lean_dec_ref(v___y_3558_);
    leanh::lean_dec(v___y_3557_);
    leanh::lean_dec_ref(v___y_3556_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(
    mut v_name_3562_: *mut leanh::LeanObject,
    mut v_bi_3563_: u8,
    mut v_type_3564_: *mut leanh::LeanObject,
    mut v_k_3565_: *mut leanh::LeanObject,
    mut v_kind_3566_: u8,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v_a_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3572_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_3572_, 0, v_k_3565_);
                v___x_3573_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_3562_,
                    v_bi_3563_,
                    v_type_3564_,
                    v___f_3572_,
                    v_kind_3566_,
                    v___y_3567_,
                    v___y_3568_,
                    v___y_3569_,
                    v___y_3570_,
                );
                if leanh::lean_obj_tag(v___x_3573_) == 0 {
                    v_a_3574_ = leanh::lean_ctor_get(v___x_3573_, 0);
                    v_isSharedCheck_3581_ = (!leanh::lean_is_exclusive(v___x_3573_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3576_ = v___x_3573_;
                        v_isShared_3577_ = v_isSharedCheck_3581_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3574_);
                        leanh::lean_dec(v___x_3573_);
                        v___x_3576_ = leanh::lean_box(0);
                        v_isShared_3577_ = v_isSharedCheck_3581_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3582_ = leanh::lean_ctor_get(v___x_3573_, 0);
                    v_isSharedCheck_3589_ = (!leanh::lean_is_exclusive(v___x_3573_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3584_ = v___x_3573_;
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3582_);
                        leanh::lean_dec(v___x_3573_);
                        v___x_3584_ = leanh::lean_box(0);
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3577_ == 0 {
                    v___x_3579_ = v___x_3576_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
                    v___x_3579_ = v_reuseFailAlloc_3580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3579_;
            }
            3 => {
                if v_isShared_3585_ == 0 {
                    v___x_3587_ = v___x_3584_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_name_3590_: *mut leanh::LeanObject,
    mut v_bi_3591_: *mut leanh::LeanObject,
    mut v_type_3592_: *mut leanh::LeanObject,
    mut v_k_3593_: *mut leanh::LeanObject,
    mut v_kind_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3600_: u8 = 0;
    let mut v_kind_boxed_3601_: u8 = 0;
    let mut v_res_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3600_ = (leanh::lean_unbox(v_bi_3591_) as u8);
    v_kind_boxed_3601_ = (leanh::lean_unbox(v_kind_3594_) as u8);
    v_res_3602_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_3590_, v_bi_boxed_3600_, v_type_3592_, v_k_3593_, v_kind_boxed_3601_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
    leanh::lean_dec(v___y_3598_);
    leanh::lean_dec_ref(v___y_3597_);
    leanh::lean_dec(v___y_3596_);
    leanh::lean_dec_ref(v___y_3595_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(
    mut v_name_3603_: *mut leanh::LeanObject,
    mut v_type_3604_: *mut leanh::LeanObject,
    mut v_k_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
    mut v___y_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3612_: u8 = 0;
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3611_ = 0;
    v___x_3612_ = 0;
    v___x_3613_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_3603_, v___x_3611_, v_type_3604_, v_k_3605_, v___x_3612_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
    return v___x_3613_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg___boxed(
    mut v_name_3614_: *mut leanh::LeanObject,
    mut v_type_3615_: *mut leanh::LeanObject,
    mut v_k_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3622_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_3614_, v_type_3615_, v_k_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
    leanh::lean_dec(v___y_3620_);
    leanh::lean_dec_ref(v___y_3619_);
    leanh::lean_dec(v___y_3618_);
    leanh::lean_dec_ref(v___y_3617_);
    return v_res_3622_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(
    mut v_msgData_3623_: *mut leanh::LeanObject,
    mut v___y_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3629_ = lean_st_ref_get(v___y_3627_);
    v_env_3630_ = leanh::lean_ctor_get(v___x_3629_, 0);
    leanh::lean_inc_ref(v_env_3630_);
    leanh::lean_dec(v___x_3629_);
    v___x_3631_ = lean_st_ref_get(v___y_3625_);
    v_mctx_3632_ = leanh::lean_ctor_get(v___x_3631_, 0);
    leanh::lean_inc_ref(v_mctx_3632_);
    leanh::lean_dec(v___x_3631_);
    v_lctx_3633_ = leanh::lean_ctor_get(v___y_3624_, 2);
    v_options_3634_ = leanh::lean_ctor_get(v___y_3626_, 2);
    leanh::lean_inc_ref(v_options_3634_);
    leanh::lean_inc_ref(v_lctx_3633_);
    v___x_3635_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3635_, 0, v_env_3630_);
    leanh::lean_ctor_set(v___x_3635_, 1, v_mctx_3632_);
    leanh::lean_ctor_set(v___x_3635_, 2, v_lctx_3633_);
    leanh::lean_ctor_set(v___x_3635_, 3, v_options_3634_);
    v___x_3636_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
    leanh::lean_ctor_set(v___x_3636_, 1, v_msgData_3623_);
    v___x_3637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3637_, 0, v___x_3636_);
    return v___x_3637_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_3638_: *mut leanh::LeanObject,
    mut v___y_3639_: *mut leanh::LeanObject,
    mut v___y_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3644_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msgData_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
    leanh::lean_dec(v___y_3642_);
    leanh::lean_dec_ref(v___y_3641_);
    leanh::lean_dec(v___y_3640_);
    leanh::lean_dec_ref(v___y_3639_);
    return v_res_3644_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(
    mut v_msg_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
    mut v___y_3647_: *mut leanh::LeanObject,
    mut v___y_3648_: *mut leanh::LeanObject,
    mut v___y_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3651_ = leanh::lean_ctor_get(v___y_3648_, 5);
                v___x_3652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1_spec__3(v_msg_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
                v_a_3653_ = leanh::lean_ctor_get(v___x_3652_, 0);
                v_isSharedCheck_3661_ = (!leanh::lean_is_exclusive(v___x_3652_)) as u8;
                if v_isSharedCheck_3661_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    v_isShared_3656_ = v_isSharedCheck_3661_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3653_);
                    leanh::lean_dec(v___x_3652_);
                    v___x_3655_ = leanh::lean_box(0);
                    v_isShared_3656_ = v_isSharedCheck_3661_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3651_);
                v___x_3657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3657_, 0, v_ref_3651_);
                leanh::lean_ctor_set(v___x_3657_, 1, v_a_3653_);
                if v_isShared_3656_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3655_, 1);
                    leanh::lean_ctor_set(v___x_3655_, 0, v___x_3657_);
                    v___x_3659_ = v___x_3655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg___boxed(
    mut v_msg_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
    mut v___y_3664_: *mut leanh::LeanObject,
    mut v___y_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
    leanh::lean_dec(v___y_3666_);
    leanh::lean_dec_ref(v___y_3665_);
    leanh::lean_dec(v___y_3664_);
    leanh::lean_dec_ref(v___y_3663_);
    return v_res_3668_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(
    mut v___x_3669_: *mut leanh::LeanObject,
    mut v_ident_3670_: *mut leanh::LeanObject,
    mut v___x_3671_: u8,
    mut v_hyps_3672_: *mut leanh::LeanObject,
    mut v___x_3673_: *mut leanh::LeanObject,
    mut v_target_3674_: *mut leanh::LeanObject,
    mut v_u_3675_: *mut leanh::LeanObject,
    mut v_k_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v_s_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
    mut v___y_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3714_: u8 = 0;
    let mut v_a_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3718_: u8 = 0;
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_3687_ = leanh::lean_ctor_get(v___y_3682_, 2);
                leanh::lean_inc_ref(v___x_3669_);
                v___x_3688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3688_, 0, v___x_3669_);
                leanh::lean_inc_ref(v_s_3681_);
                leanh::lean_inc_ref(v_lctx_3687_);
                v___x_3689_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                    v_ident_3670_,
                    v_lctx_3687_,
                    v_s_3681_,
                    v___x_3688_,
                    v___x_3671_,
                    v___y_3682_,
                    v___y_3683_,
                    v___y_3684_,
                    v___y_3685_,
                );
                if leanh::lean_obj_tag(v___x_3689_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3689_, 1);
                    leanh::lean_inc_ref(v_s_3681_);
                    leanh::lean_inc_ref(v_hyps_3672_);
                    v___x_3690_ = l_Lean_Expr_app___override(v_hyps_3672_, v_s_3681_);
                    leanh::lean_inc_ref_n(v___x_3673_, 2);
                    v___x_3691_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
                        v___x_3673_,
                        v___x_3690_,
                    );
                    v___x_3692_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3693_ = lean_mk_empty_array_with_capacity(v___x_3692_);
                    v___x_3694_ = lean_array_push(v___x_3693_, v_s_3681_);
                    v___x_3695_ = 0;
                    leanh::lean_inc_ref(v_target_3674_);
                    v___x_3696_ =
                        l_Lean_Expr_betaRev(v_target_3674_, v___x_3694_, v___x_3695_, v___x_3695_);
                    leanh::lean_inc(v_u_3675_);
                    v___x_3697_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_3697_, 0, v_u_3675_);
                    leanh::lean_ctor_set(v___x_3697_, 1, v___x_3673_);
                    leanh::lean_ctor_set(v___x_3697_, 2, v___x_3691_);
                    leanh::lean_ctor_set(v___x_3697_, 3, v___x_3696_);
                    leanh::lean_inc(v___y_3685_);
                    leanh::lean_inc_ref(v___y_3684_);
                    leanh::lean_inc(v___y_3683_);
                    leanh::lean_inc_ref(v___y_3682_);
                    leanh::lean_inc(v___y_3680_);
                    leanh::lean_inc_ref(v___y_3679_);
                    leanh::lean_inc(v___y_3678_);
                    leanh::lean_inc_ref(v___y_3677_);
                    v___x_3698_ = leanh::lean_apply_10(
                        v_k_3676_,
                        v___x_3697_,
                        v___y_3677_,
                        v___y_3678_,
                        v___y_3679_,
                        v___y_3680_,
                        v___y_3682_,
                        v___y_3683_,
                        v___y_3684_,
                        v___y_3685_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3698_) == 0 {
                        v_a_3699_ = leanh::lean_ctor_get(v___x_3698_, 0);
                        leanh::lean_inc(v_a_3699_);
                        leanh::lean_dec_ref_known(v___x_3698_, 1);
                        v___x_3700_ = 1;
                        v___x_3701_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_3694_,
                            v_a_3699_,
                            v___x_3695_,
                            v___x_3671_,
                            v___x_3695_,
                            v___x_3671_,
                            v___x_3700_,
                            v___y_3682_,
                            v___y_3683_,
                            v___y_3684_,
                            v___y_3685_,
                        );
                        leanh::lean_dec_ref(v___x_3694_);
                        if leanh::lean_obj_tag(v___x_3701_) == 0 {
                            v_a_3702_ = leanh::lean_ctor_get(v___x_3701_, 0);
                            v_isSharedCheck_3714_ =
                                (!leanh::lean_is_exclusive(v___x_3701_)) as u8;
                            if v_isSharedCheck_3714_ == 0 {
                                v___x_3704_ = v___x_3701_;
                                v_isShared_3705_ = v_isSharedCheck_3714_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3702_);
                                leanh::lean_dec(v___x_3701_);
                                v___x_3704_ = leanh::lean_box(0);
                                v_isShared_3705_ = v_isSharedCheck_3714_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_u_3675_);
                            leanh::lean_dec_ref(v_target_3674_);
                            leanh::lean_dec_ref(v___x_3673_);
                            leanh::lean_dec_ref(v_hyps_3672_);
                            leanh::lean_dec_ref(v___x_3669_);
                            return v___x_3701_;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3694_);
                        leanh::lean_dec(v_u_3675_);
                        leanh::lean_dec_ref(v_target_3674_);
                        leanh::lean_dec_ref(v___x_3673_);
                        leanh::lean_dec_ref(v_hyps_3672_);
                        leanh::lean_dec_ref(v___x_3669_);
                        return v___x_3698_;
                    }
                } else {
                    leanh::lean_dec_ref(v_s_3681_);
                    leanh::lean_dec_ref(v_k_3676_);
                    leanh::lean_dec(v_u_3675_);
                    leanh::lean_dec_ref(v_target_3674_);
                    leanh::lean_dec_ref(v___x_3673_);
                    leanh::lean_dec_ref(v_hyps_3672_);
                    leanh::lean_dec_ref(v___x_3669_);
                    v_a_3715_ = leanh::lean_ctor_get(v___x_3689_, 0);
                    v_isSharedCheck_3722_ = (!leanh::lean_is_exclusive(v___x_3689_)) as u8;
                    if v_isSharedCheck_3722_ == 0 {
                        v___x_3717_ = v___x_3689_;
                        v_isShared_3718_ = v_isSharedCheck_3722_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3715_);
                        leanh::lean_dec(v___x_3689_);
                        v___x_3717_ = leanh::lean_box(0);
                        v_isShared_3718_ = v_isSharedCheck_3722_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3706_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__0___closed__1;
                v___x_3707_ = leanh::lean_box(0);
                v___x_3708_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3708_, 0, v_u_3675_);
                leanh::lean_ctor_set(v___x_3708_, 1, v___x_3707_);
                v___x_3709_ = l_Lean_mkConst(v___x_3706_, v___x_3708_);
                v___x_3710_ = l_Lean_mkApp5(
                    v___x_3709_,
                    v___x_3673_,
                    v___x_3669_,
                    v_hyps_3672_,
                    v_target_3674_,
                    v_a_3702_,
                );
                if v_isShared_3705_ == 0 {
                    leanh::lean_ctor_set(v___x_3704_, 0, v___x_3710_);
                    v___x_3712_ = v___x_3704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
                    v___x_3712_ = v_reuseFailAlloc_3713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3712_;
            }
            3 => {
                if v_isShared_3718_ == 0 {
                    v___x_3720_ = v___x_3717_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
                    v___x_3720_ = v_reuseFailAlloc_3721_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3723_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_ident_3724_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_3725_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_hyps_3726_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_3727_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_target_3728_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_u_3729_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_k_3730_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_3731_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_3732_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_3733_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_3734_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_s_3735_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3736_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3737_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3738_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3739_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3740_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_20692__boxed_3741_: u8 = 0;
    let mut v_res_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_20692__boxed_3741_ = (leanh::lean_unbox(v___x_3725_) as u8);
    v_res_3742_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0(v___x_3723_, v_ident_3724_, v___x_20692__boxed_3741_, v_hyps_3726_, v___x_3727_, v_target_3728_, v_u_3729_, v_k_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v_s_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    leanh::lean_dec(v___y_3739_);
    leanh::lean_dec_ref(v___y_3738_);
    leanh::lean_dec(v___y_3737_);
    leanh::lean_dec_ref(v___y_3736_);
    leanh::lean_dec(v___y_3734_);
    leanh::lean_dec_ref(v___y_3733_);
    leanh::lean_dec(v___y_3732_);
    leanh::lean_dec_ref(v___y_3731_);
    return v_res_3742_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(
    mut v_goal_3743_: *mut leanh::LeanObject,
    mut v_ident_3744_: *mut leanh::LeanObject,
    mut v_k_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3760_: u8 = 0;
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3764_: u8 = 0;
    let mut v_u_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: u8 = 0;
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3765_ = leanh::lean_ctor_get(v_goal_3743_, 0);
                leanh::lean_inc(v_u_3765_);
                v_00_u03c3s_3766_ = leanh::lean_ctor_get(v_goal_3743_, 1);
                leanh::lean_inc_ref_n(v_00_u03c3s_3766_, 2);
                v_hyps_3767_ = leanh::lean_ctor_get(v_goal_3743_, 2);
                leanh::lean_inc_ref(v_hyps_3767_);
                v_target_3768_ = leanh::lean_ctor_get(v_goal_3743_, 3);
                leanh::lean_inc_ref(v_target_3768_);
                leanh::lean_dec_ref(v_goal_3743_);
                leanh::lean_inc(v___y_3753_);
                leanh::lean_inc_ref(v___y_3752_);
                leanh::lean_inc(v___y_3751_);
                leanh::lean_inc_ref(v___y_3750_);
                v___x_3769_ = lean_whnf(
                    v_00_u03c3s_3766_,
                    v___y_3750_,
                    v___y_3751_,
                    v___y_3752_,
                    v___y_3753_,
                );
                if leanh::lean_obj_tag(v___x_3769_) == 0 {
                    v_a_3770_ = leanh::lean_ctor_get(v___x_3769_, 0);
                    leanh::lean_inc(v_a_3770_);
                    leanh::lean_dec_ref_known(v___x_3769_, 1);
                    v___x_3771_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__2;
                    v___x_3772_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3773_ = l_Lean_Expr_isAppOfArity(v_a_3770_, v___x_3771_, v___x_3772_);
                    if v___x_3773_ == 0 {
                        leanh::lean_dec(v_a_3770_);
                        leanh::lean_dec_ref(v_target_3768_);
                        leanh::lean_dec_ref(v_hyps_3767_);
                        leanh::lean_dec(v_u_3765_);
                        leanh::lean_dec_ref(v_k_3745_);
                        leanh::lean_dec(v_ident_3744_);
                        v___x_3774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__4);
                        v___x_3775_ = l_Lean_MessageData_ofExpr(v_00_u03c3s_3766_);
                        v___x_3776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3776_, 0, v___x_3774_);
                        leanh::lean_ctor_set(v___x_3776_, 1, v___x_3775_);
                        v___x_3777_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_3776_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
                        v___y_3756_ = v___x_3777_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_00_u03c3s_3766_);
                        v___x_3778_ = l_Lean_Expr_appFn_x21(v_a_3770_);
                        v___x_3779_ = l_Lean_Expr_appArg_x21(v___x_3778_);
                        leanh::lean_dec_ref(v___x_3778_);
                        v___x_3780_ = l_Lean_Expr_appArg_x21(v_a_3770_);
                        leanh::lean_dec(v_a_3770_);
                        v___x_3781_ = leanh::lean_box((v___x_3773_) as usize);
                        leanh::lean_inc(v___y_3749_);
                        leanh::lean_inc_ref(v___y_3748_);
                        leanh::lean_inc(v___y_3747_);
                        leanh::lean_inc_ref(v___y_3746_);
                        leanh::lean_inc_n(v_ident_3744_, 2);
                        leanh::lean_inc_ref(v___x_3779_);
                        v___f_3782_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___lam__0___boxed as *mut core::ffi::c_void, 18, 12);
                        leanh::lean_closure_set(v___f_3782_, 0, v___x_3779_);
                        leanh::lean_closure_set(v___f_3782_, 1, v_ident_3744_);
                        leanh::lean_closure_set(v___f_3782_, 2, v___x_3781_);
                        leanh::lean_closure_set(v___f_3782_, 3, v_hyps_3767_);
                        leanh::lean_closure_set(v___f_3782_, 4, v___x_3780_);
                        leanh::lean_closure_set(v___f_3782_, 5, v_target_3768_);
                        leanh::lean_closure_set(v___f_3782_, 6, v_u_3765_);
                        leanh::lean_closure_set(v___f_3782_, 7, v_k_3745_);
                        leanh::lean_closure_set(v___f_3782_, 8, v___y_3746_);
                        leanh::lean_closure_set(v___f_3782_, 9, v___y_3747_);
                        leanh::lean_closure_set(v___f_3782_, 10, v___y_3748_);
                        leanh::lean_closure_set(v___f_3782_, 11, v___y_3749_);
                        v___x_3783_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        v___x_3784_ = l_Lean_Syntax_isOfKind(v_ident_3744_, v___x_3783_);
                        if v___x_3784_ == 0 {
                            leanh::lean_dec(v_ident_3744_);
                            v___x_3785_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6;
                            v___x_3786_ =
                                l_Lean_Core_mkFreshUserName(v___x_3785_, v___y_3752_, v___y_3753_);
                            if leanh::lean_obj_tag(v___x_3786_) == 0 {
                                v_a_3787_ = leanh::lean_ctor_get(v___x_3786_, 0);
                                leanh::lean_inc(v_a_3787_);
                                leanh::lean_dec_ref_known(v___x_3786_, 1);
                                v___x_3788_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_3787_, v___x_3779_, v___f_3782_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
                                v___y_3756_ = v___x_3788_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___f_3782_);
                                leanh::lean_dec_ref(v___x_3779_);
                                v_a_3789_ = leanh::lean_ctor_get(v___x_3786_, 0);
                                v_isSharedCheck_3796_ =
                                    (!leanh::lean_is_exclusive(v___x_3786_)) as u8;
                                if v_isSharedCheck_3796_ == 0 {
                                    v___x_3791_ = v___x_3786_;
                                    v_isShared_3792_ = v_isSharedCheck_3796_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3789_);
                                    leanh::lean_dec(v___x_3786_);
                                    v___x_3791_ = leanh::lean_box(0);
                                    v_isShared_3792_ = v_isSharedCheck_3796_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3797_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3798_ = l_Lean_Syntax_getArg(v_ident_3744_, v___x_3797_);
                            leanh::lean_dec(v_ident_3744_);
                            v___x_3799_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29;
                            leanh::lean_inc(v___x_3798_);
                            v___x_3800_ = l_Lean_Syntax_isOfKind(v___x_3798_, v___x_3799_);
                            if v___x_3800_ == 0 {
                                leanh::lean_dec(v___x_3798_);
                                v___x_3801_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___redArg___lam__3___closed__6;
                                v___x_3802_ = l_Lean_Core_mkFreshUserName(
                                    v___x_3801_,
                                    v___y_3752_,
                                    v___y_3753_,
                                );
                                if leanh::lean_obj_tag(v___x_3802_) == 0 {
                                    v_a_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                                    leanh::lean_inc(v_a_3803_);
                                    leanh::lean_dec_ref_known(v___x_3802_, 1);
                                    v___x_3804_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_a_3803_, v___x_3779_, v___f_3782_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
                                    v___y_3756_ = v___x_3804_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___f_3782_);
                                    leanh::lean_dec_ref(v___x_3779_);
                                    v_a_3805_ = leanh::lean_ctor_get(v___x_3802_, 0);
                                    v_isSharedCheck_3812_ =
                                        (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                                    if v_isSharedCheck_3812_ == 0 {
                                        v___x_3807_ = v___x_3802_;
                                        v_isShared_3808_ = v_isSharedCheck_3812_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3805_);
                                        leanh::lean_dec(v___x_3802_);
                                        v___x_3807_ = leanh::lean_box(0);
                                        v_isShared_3808_ = v_isSharedCheck_3812_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                v___x_3813_ = l_Lean_TSyntax_getId(v___x_3798_);
                                leanh::lean_dec(v___x_3798_);
                                v___x_3814_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v___x_3813_, v___x_3779_, v___f_3782_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
                                v___y_3756_ = v___x_3814_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_target_3768_);
                    leanh::lean_dec_ref(v_hyps_3767_);
                    leanh::lean_dec_ref(v_00_u03c3s_3766_);
                    leanh::lean_dec(v_u_3765_);
                    leanh::lean_dec_ref(v_k_3745_);
                    leanh::lean_dec(v_ident_3744_);
                    return v___x_3769_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3756_) == 0 {
                    return v___y_3756_;
                } else {
                    v_a_3757_ = leanh::lean_ctor_get(v___y_3756_, 0);
                    v_isSharedCheck_3764_ = (!leanh::lean_is_exclusive(v___y_3756_)) as u8;
                    if v_isSharedCheck_3764_ == 0 {
                        v___x_3759_ = v___y_3756_;
                        v_isShared_3760_ = v_isSharedCheck_3764_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3757_);
                        leanh::lean_dec(v___y_3756_);
                        v___x_3759_ = leanh::lean_box(0);
                        v_isShared_3760_ = v_isSharedCheck_3764_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3760_ == 0 {
                    v___x_3762_ = v___x_3759_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
                    v___x_3762_ = v_reuseFailAlloc_3763_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3762_;
            }
            4 => {
                if v_isShared_3792_ == 0 {
                    v___x_3794_ = v___x_3791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
                    v___x_3794_ = v_reuseFailAlloc_3795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3794_;
            }
            6 => {
                if v_isShared_3808_ == 0 {
                    v___x_3810_ = v___x_3807_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
                    v___x_3810_ = v_reuseFailAlloc_3811_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1___boxed(
    mut v_goal_3815_: *mut leanh::LeanObject,
    mut v_ident_3816_: *mut leanh::LeanObject,
    mut v_k_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
    mut v___y_3819_: *mut leanh::LeanObject,
    mut v___y_3820_: *mut leanh::LeanObject,
    mut v___y_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3827_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_goal_3815_, v_ident_3816_, v_k_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
    leanh::lean_dec(v___y_3825_);
    leanh::lean_dec_ref(v___y_3824_);
    leanh::lean_dec(v___y_3823_);
    leanh::lean_dec_ref(v___y_3822_);
    leanh::lean_dec(v___y_3821_);
    leanh::lean_dec_ref(v___y_3820_);
    leanh::lean_dec(v___y_3819_);
    leanh::lean_dec_ref(v___y_3818_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(
    mut v___x_3828_: *mut leanh::LeanObject,
    mut v_snd_3829_: *mut leanh::LeanObject,
    mut v_ident_3830_: *mut leanh::LeanObject,
    mut v_fst_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
    mut v___y_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3841_ = lean_st_mk_ref(v___x_3828_);
                leanh::lean_inc(v___x_3841_);
                v___f_3842_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    1,
                );
                leanh::lean_closure_set(v___f_3842_, 0, v___x_3841_);
                v___x_3843_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1(v_snd_3829_, v_ident_3830_, v___f_3842_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
                if leanh::lean_obj_tag(v___x_3843_) == 0 {
                    v_a_3844_ = leanh::lean_ctor_get(v___x_3843_, 0);
                    leanh::lean_inc(v_a_3844_);
                    leanh::lean_dec_ref_known(v___x_3843_, 1);
                    v___x_3845_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_3831_, v_a_3844_, v___y_3837_);
                    leanh::lean_dec_ref(v___x_3845_);
                    v___x_3846_ = lean_st_ref_get(v___x_3841_);
                    leanh::lean_dec(v___x_3841_);
                    v___x_3847_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_3846_,
                        v___y_3833_,
                        v___y_3836_,
                        v___y_3837_,
                        v___y_3838_,
                        v___y_3839_,
                    );
                    return v___x_3847_;
                } else {
                    leanh::lean_dec(v___x_3841_);
                    leanh::lean_dec(v_fst_3831_);
                    v_a_3848_ = leanh::lean_ctor_get(v___x_3843_, 0);
                    v_isSharedCheck_3855_ = (!leanh::lean_is_exclusive(v___x_3843_)) as u8;
                    if v_isSharedCheck_3855_ == 0 {
                        v___x_3850_ = v___x_3843_;
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3848_);
                        leanh::lean_dec(v___x_3843_);
                        v___x_3850_ = leanh::lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
                    v___x_3853_ = v_reuseFailAlloc_3854_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed(
    mut v___x_3856_: *mut leanh::LeanObject,
    mut v_snd_3857_: *mut leanh::LeanObject,
    mut v_ident_3858_: *mut leanh::LeanObject,
    mut v_fst_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
    mut v___y_3866_: *mut leanh::LeanObject,
    mut v___y_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1(
        v___x_3856_,
        v_snd_3857_,
        v_ident_3858_,
        v_fst_3859_,
        v___y_3860_,
        v___y_3861_,
        v___y_3862_,
        v___y_3863_,
        v___y_3864_,
        v___y_3865_,
        v___y_3866_,
        v___y_3867_,
    );
    leanh::lean_dec(v___y_3867_);
    leanh::lean_dec_ref(v___y_3866_);
    leanh::lean_dec(v___y_3865_);
    leanh::lean_dec_ref(v___y_3864_);
    leanh::lean_dec(v___y_3863_);
    leanh::lean_dec_ref(v___y_3862_);
    leanh::lean_dec(v___y_3861_);
    leanh::lean_dec_ref(v___y_3860_);
    return v_res_3869_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(
    mut v_k_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v_b_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3879_);
    leanh::lean_inc_ref(v___y_3878_);
    leanh::lean_inc(v___y_3877_);
    leanh::lean_inc_ref(v___y_3876_);
    leanh::lean_inc(v___y_3874_);
    leanh::lean_inc_ref(v___y_3873_);
    leanh::lean_inc(v___y_3872_);
    leanh::lean_inc_ref(v___y_3871_);
    v___x_3881_ = leanh::lean_apply_10(
        v_k_3870_,
        v_b_3875_,
        v___y_3871_,
        v___y_3872_,
        v___y_3873_,
        v___y_3874_,
        v___y_3876_,
        v___y_3877_,
        v___y_3878_,
        v___y_3879_,
        leanh::lean_box(0),
    );
    return v___x_3881_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed(
    mut v_k_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
    mut v___y_3885_: *mut leanh::LeanObject,
    mut v___y_3886_: *mut leanh::LeanObject,
    mut v_b_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
    mut v___y_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0(v_k_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v_b_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
    leanh::lean_dec(v___y_3891_);
    leanh::lean_dec_ref(v___y_3890_);
    leanh::lean_dec(v___y_3889_);
    leanh::lean_dec_ref(v___y_3888_);
    leanh::lean_dec(v___y_3886_);
    leanh::lean_dec_ref(v___y_3885_);
    leanh::lean_dec(v___y_3884_);
    leanh::lean_dec_ref(v___y_3883_);
    return v_res_3893_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(
    mut v_name_3894_: *mut leanh::LeanObject,
    mut v_type_3895_: *mut leanh::LeanObject,
    mut v_val_3896_: *mut leanh::LeanObject,
    mut v_k_3897_: *mut leanh::LeanObject,
    mut v_nondep_3898_: u8,
    mut v_kind_3899_: u8,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3903_);
                leanh::lean_inc_ref(v___y_3902_);
                leanh::lean_inc(v___y_3901_);
                leanh::lean_inc_ref(v___y_3900_);
                v___f_3909_ = leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                leanh::lean_closure_set(v___f_3909_, 0, v_k_3897_);
                leanh::lean_closure_set(v___f_3909_, 1, v___y_3900_);
                leanh::lean_closure_set(v___f_3909_, 2, v___y_3901_);
                leanh::lean_closure_set(v___f_3909_, 3, v___y_3902_);
                leanh::lean_closure_set(v___f_3909_, 4, v___y_3903_);
                v___x_3910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_3894_,
                    v_type_3895_,
                    v_val_3896_,
                    v___f_3909_,
                    v_nondep_3898_,
                    v_kind_3899_,
                    v___y_3904_,
                    v___y_3905_,
                    v___y_3906_,
                    v___y_3907_,
                );
                if leanh::lean_obj_tag(v___x_3910_) == 0 {
                    return v___x_3910_;
                } else {
                    v_a_3911_ = leanh::lean_ctor_get(v___x_3910_, 0);
                    v_isSharedCheck_3918_ = (!leanh::lean_is_exclusive(v___x_3910_)) as u8;
                    if v_isSharedCheck_3918_ == 0 {
                        v___x_3913_ = v___x_3910_;
                        v_isShared_3914_ = v_isSharedCheck_3918_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3911_);
                        leanh::lean_dec(v___x_3910_);
                        v___x_3913_ = leanh::lean_box(0);
                        v_isShared_3914_ = v_isSharedCheck_3918_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3914_ == 0 {
                    v___x_3916_ = v___x_3913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg___boxed(
    mut v_name_3919_: *mut leanh::LeanObject,
    mut v_type_3920_: *mut leanh::LeanObject,
    mut v_val_3921_: *mut leanh::LeanObject,
    mut v_k_3922_: *mut leanh::LeanObject,
    mut v_nondep_3923_: *mut leanh::LeanObject,
    mut v_kind_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
    mut v___y_3927_: *mut leanh::LeanObject,
    mut v___y_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_3934_: u8 = 0;
    let mut v_kind_boxed_3935_: u8 = 0;
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3934_ = (leanh::lean_unbox(v_nondep_3923_) as u8);
    v_kind_boxed_3935_ = (leanh::lean_unbox(v_kind_3924_) as u8);
    v_res_3936_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_3919_, v_type_3920_, v_val_3921_, v_k_3922_, v_nondep_boxed_3934_, v_kind_boxed_3935_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
    leanh::lean_dec(v___y_3932_);
    leanh::lean_dec_ref(v___y_3931_);
    leanh::lean_dec(v___y_3930_);
    leanh::lean_dec_ref(v___y_3929_);
    leanh::lean_dec(v___y_3928_);
    leanh::lean_dec_ref(v___y_3927_);
    leanh::lean_dec(v___y_3926_);
    leanh::lean_dec_ref(v___y_3925_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(
    mut v___y_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v_r_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_unused_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3939_ = lean_st_ref_get(v___y_3937_);
                v_ngen_3940_ = leanh::lean_ctor_get(v___x_3939_, 2);
                leanh::lean_inc_ref(v_ngen_3940_);
                leanh::lean_dec(v___x_3939_);
                v_namePrefix_3941_ = leanh::lean_ctor_get(v_ngen_3940_, 0);
                v_idx_3942_ = leanh::lean_ctor_get(v_ngen_3940_, 1);
                v_isSharedCheck_3971_ = (!leanh::lean_is_exclusive(v_ngen_3940_)) as u8;
                if v_isSharedCheck_3971_ == 0 {
                    v___x_3944_ = v_ngen_3940_;
                    v_isShared_3945_ = v_isSharedCheck_3971_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_idx_3942_);
                    leanh::lean_inc(v_namePrefix_3941_);
                    leanh::lean_dec(v_ngen_3940_);
                    v___x_3944_ = leanh::lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3946_ = lean_st_ref_take(v___y_3937_);
                v_env_3947_ = leanh::lean_ctor_get(v___x_3946_, 0);
                v_nextMacroScope_3948_ = leanh::lean_ctor_get(v___x_3946_, 1);
                v_auxDeclNGen_3949_ = leanh::lean_ctor_get(v___x_3946_, 3);
                v_traceState_3950_ = leanh::lean_ctor_get(v___x_3946_, 4);
                v_cache_3951_ = leanh::lean_ctor_get(v___x_3946_, 5);
                v_messages_3952_ = leanh::lean_ctor_get(v___x_3946_, 6);
                v_infoState_3953_ = leanh::lean_ctor_get(v___x_3946_, 7);
                v_snapshotTasks_3954_ = leanh::lean_ctor_get(v___x_3946_, 8);
                v_isSharedCheck_3969_ = (!leanh::lean_is_exclusive(v___x_3946_)) as u8;
                if v_isSharedCheck_3969_ == 0 {
                    v_unused_3970_ = leanh::lean_ctor_get(v___x_3946_, 2);
                    leanh::lean_dec(v_unused_3970_);
                    v___x_3956_ = v___x_3946_;
                    v_isShared_3957_ = v_isSharedCheck_3969_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3954_);
                    leanh::lean_inc(v_infoState_3953_);
                    leanh::lean_inc(v_messages_3952_);
                    leanh::lean_inc(v_cache_3951_);
                    leanh::lean_inc(v_traceState_3950_);
                    leanh::lean_inc(v_auxDeclNGen_3949_);
                    leanh::lean_inc(v_nextMacroScope_3948_);
                    leanh::lean_inc(v_env_3947_);
                    leanh::lean_dec(v___x_3946_);
                    v___x_3956_ = leanh::lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3969_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_idx_3942_);
                leanh::lean_inc(v_namePrefix_3941_);
                v_r_3958_ = l_Lean_Name_num___override(v_namePrefix_3941_, v_idx_3942_);
                v___x_3959_ = leanh::lean_unsigned_to_nat(1);
                v___x_3960_ = lean_nat_add(v_idx_3942_, v___x_3959_);
                leanh::lean_dec(v_idx_3942_);
                if v_isShared_3945_ == 0 {
                    leanh::lean_ctor_set(v___x_3944_, 1, v___x_3960_);
                    v___x_3962_ = v___x_3944_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_namePrefix_3941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 1, v___x_3960_);
                    v___x_3962_ = v_reuseFailAlloc_3968_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3957_ == 0 {
                    leanh::lean_ctor_set(v___x_3956_, 2, v___x_3962_);
                    v___x_3964_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_env_3947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_nextMacroScope_3948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 2, v___x_3962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_auxDeclNGen_3949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_traceState_3950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 5, v_cache_3951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 6, v_messages_3952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 7, v_infoState_3953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 8, v_snapshotTasks_3954_);
                    v___x_3964_ = v_reuseFailAlloc_3967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3965_ = lean_st_ref_set(v___y_3937_, v___x_3964_);
                v___x_3966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3966_, 0, v_r_3958_);
                return v___x_3966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg___boxed(
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_3972_);
    leanh::lean_dec(v___y_3972_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(
    mut v_body_3975_: *mut leanh::LeanObject,
    mut v_u_3976_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3977_: *mut leanh::LeanObject,
    mut v_hyps_3978_: *mut leanh::LeanObject,
    mut v_k_3979_: *mut leanh::LeanObject,
    mut v_val_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = lean_expr_instantiate1(v_body_3975_, v_val_3980_);
    v___x_3991_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3991_, 0, v_u_3976_);
    leanh::lean_ctor_set(v___x_3991_, 1, v_00_u03c3s_3977_);
    leanh::lean_ctor_set(v___x_3991_, 2, v_hyps_3978_);
    leanh::lean_ctor_set(v___x_3991_, 3, v___x_3990_);
    leanh::lean_inc(v___y_3988_);
    leanh::lean_inc_ref(v___y_3987_);
    leanh::lean_inc(v___y_3986_);
    leanh::lean_inc_ref(v___y_3985_);
    leanh::lean_inc(v___y_3984_);
    leanh::lean_inc_ref(v___y_3983_);
    leanh::lean_inc(v___y_3982_);
    leanh::lean_inc_ref(v___y_3981_);
    v___x_3992_ = leanh::lean_apply_10(
        v_k_3979_,
        v___x_3991_,
        v___y_3981_,
        v___y_3982_,
        v___y_3983_,
        v___y_3984_,
        v___y_3985_,
        v___y_3986_,
        v___y_3987_,
        v___y_3988_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_3992_) == 0 {
        let mut v_a_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3997_: u8 = 0;
        let mut v___x_3998_: u8 = 0;
        let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3993_ = leanh::lean_ctor_get(v___x_3992_, 0);
        leanh::lean_inc(v_a_3993_);
        leanh::lean_dec_ref_known(v___x_3992_, 1);
        v___x_3994_ = leanh::lean_unsigned_to_nat(1);
        v___x_3995_ = lean_mk_empty_array_with_capacity(v___x_3994_);
        v___x_3996_ = lean_array_push(v___x_3995_, v_val_3980_);
        v___x_3997_ = 1;
        v___x_3998_ = 1;
        v___x_3999_ = l_Lean_Meta_mkLetFVars(
            v___x_3996_,
            v_a_3993_,
            v___x_3997_,
            v___x_3997_,
            v___x_3998_,
            v___y_3985_,
            v___y_3986_,
            v___y_3987_,
            v___y_3988_,
        );
        leanh::lean_dec_ref(v___x_3996_);
        return v___x_3999_;
    } else {
        leanh::lean_dec_ref(v_val_3980_);
        return v___x_3992_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed(
    mut v_body_4000_: *mut leanh::LeanObject,
    mut v_u_4001_: *mut leanh::LeanObject,
    mut v_00_u03c3s_4002_: *mut leanh::LeanObject,
    mut v_hyps_4003_: *mut leanh::LeanObject,
    mut v_k_4004_: *mut leanh::LeanObject,
    mut v_val_4005_: *mut leanh::LeanObject,
    mut v___y_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
    mut v___y_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4015_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0(v_body_4000_, v_u_4001_, v_00_u03c3s_4002_, v_hyps_4003_, v_k_4004_, v_val_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
    leanh::lean_dec(v___y_4013_);
    leanh::lean_dec_ref(v___y_4012_);
    leanh::lean_dec(v___y_4011_);
    leanh::lean_dec_ref(v___y_4010_);
    leanh::lean_dec(v___y_4009_);
    leanh::lean_dec_ref(v___y_4008_);
    leanh::lean_dec(v___y_4007_);
    leanh::lean_dec_ref(v___y_4006_);
    leanh::lean_dec_ref(v_body_4000_);
    return v_res_4015_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(
    mut v_goal_4023_: *mut leanh::LeanObject,
    mut v_ident_4024_: *mut leanh::LeanObject,
    mut v_k_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
    mut v___y_4028_: *mut leanh::LeanObject,
    mut v___y_4029_: *mut leanh::LeanObject,
    mut v___y_4030_: *mut leanh::LeanObject,
    mut v___y_4031_: *mut leanh::LeanObject,
    mut v___y_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: u8 = 0;
    let mut v_declName_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: u8 = 0;
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4083_: u8 = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4087_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyp_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_H_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4111_: u8 = 0;
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v_reuseFailAlloc_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_4035_ = leanh::lean_ctor_get(v_goal_4023_, 0);
                v_00_u03c3s_4036_ = leanh::lean_ctor_get(v_goal_4023_, 1);
                v_hyps_4037_ = leanh::lean_ctor_get(v_goal_4023_, 2);
                v_target_4038_ = leanh::lean_ctor_get(v_goal_4023_, 3);
                v_isSharedCheck_4149_ = (!leanh::lean_is_exclusive(v_goal_4023_)) as u8;
                if v_isSharedCheck_4149_ == 0 {
                    v___x_4040_ = v_goal_4023_;
                    v_isShared_4041_ = v_isSharedCheck_4149_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_target_4038_);
                    leanh::lean_inc(v_hyps_4037_);
                    leanh::lean_inc(v_00_u03c3s_4036_);
                    leanh::lean_inc(v_u_4035_);
                    leanh::lean_dec(v_goal_4023_);
                    v___x_4040_ = leanh::lean_box(0);
                    v_isShared_4041_ = v_isSharedCheck_4149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4042_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__24;
                v___x_4043_ = leanh::lean_unsigned_to_nat(3);
                v___x_4044_ = l_Lean_Expr_isAppOfArity(v_target_4038_, v___x_4042_, v___x_4043_);
                if v___x_4044_ == 0 {
                    leanh::lean_del_object(v___x_4040_);
                    if leanh::lean_obj_tag(v_target_4038_) == 8 {
                        v_declName_4045_ = leanh::lean_ctor_get(v_target_4038_, 0);
                        leanh::lean_inc(v_declName_4045_);
                        v_type_4046_ = leanh::lean_ctor_get(v_target_4038_, 1);
                        leanh::lean_inc_ref(v_type_4046_);
                        v_value_4047_ = leanh::lean_ctor_get(v_target_4038_, 2);
                        leanh::lean_inc_ref(v_value_4047_);
                        v_body_4048_ = leanh::lean_ctor_get(v_target_4038_, 3);
                        leanh::lean_inc_ref(v_body_4048_);
                        leanh::lean_dec_ref_known(v_target_4038_, 4);
                        v___f_4049_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___lam__0___boxed as *mut core::ffi::c_void, 15, 5);
                        leanh::lean_closure_set(v___f_4049_, 0, v_body_4048_);
                        leanh::lean_closure_set(v___f_4049_, 1, v_u_4035_);
                        leanh::lean_closure_set(v___f_4049_, 2, v_00_u03c3s_4036_);
                        leanh::lean_closure_set(v___f_4049_, 3, v_hyps_4037_);
                        leanh::lean_closure_set(v___f_4049_, 4, v_k_4025_);
                        v___x_4062_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                        leanh::lean_inc(v_ident_4024_);
                        v___x_4063_ = l_Lean_Syntax_isOfKind(v_ident_4024_, v___x_4062_);
                        if v___x_4063_ == 0 {
                            leanh::lean_dec(v_ident_4024_);
                            v___x_4064_ = l_Lean_Core_mkFreshUserName(
                                v_declName_4045_,
                                v___y_4032_,
                                v___y_4033_,
                            );
                            if leanh::lean_obj_tag(v___x_4064_) == 0 {
                                v_a_4065_ = leanh::lean_ctor_get(v___x_4064_, 0);
                                leanh::lean_inc(v_a_4065_);
                                leanh::lean_dec_ref_known(v___x_4064_, 1);
                                v_name_4051_ = v_a_4065_;
                                v___y_4052_ = v___y_4026_;
                                v___y_4053_ = v___y_4027_;
                                v___y_4054_ = v___y_4028_;
                                v___y_4055_ = v___y_4029_;
                                v___y_4056_ = v___y_4030_;
                                v___y_4057_ = v___y_4031_;
                                v___y_4058_ = v___y_4032_;
                                v___y_4059_ = v___y_4033_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___f_4049_);
                                leanh::lean_dec_ref(v_value_4047_);
                                leanh::lean_dec_ref(v_type_4046_);
                                v_a_4066_ = leanh::lean_ctor_get(v___x_4064_, 0);
                                v_isSharedCheck_4073_ =
                                    (!leanh::lean_is_exclusive(v___x_4064_)) as u8;
                                if v_isSharedCheck_4073_ == 0 {
                                    v___x_4068_ = v___x_4064_;
                                    v_isShared_4069_ = v_isSharedCheck_4073_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4066_);
                                    leanh::lean_dec(v___x_4064_);
                                    v___x_4068_ = leanh::lean_box(0);
                                    v_isShared_4069_ = v_isSharedCheck_4073_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4074_ = leanh::lean_unsigned_to_nat(0);
                            v_name_4075_ = l_Lean_Syntax_getArg(v_ident_4024_, v___x_4074_);
                            leanh::lean_dec(v_ident_4024_);
                            v___x_4076_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__29;
                            leanh::lean_inc(v_name_4075_);
                            v___x_4077_ = l_Lean_Syntax_isOfKind(v_name_4075_, v___x_4076_);
                            if v___x_4077_ == 0 {
                                leanh::lean_dec(v_name_4075_);
                                v___x_4078_ = l_Lean_Core_mkFreshUserName(
                                    v_declName_4045_,
                                    v___y_4032_,
                                    v___y_4033_,
                                );
                                if leanh::lean_obj_tag(v___x_4078_) == 0 {
                                    v_a_4079_ = leanh::lean_ctor_get(v___x_4078_, 0);
                                    leanh::lean_inc(v_a_4079_);
                                    leanh::lean_dec_ref_known(v___x_4078_, 1);
                                    v_name_4051_ = v_a_4079_;
                                    v___y_4052_ = v___y_4026_;
                                    v___y_4053_ = v___y_4027_;
                                    v___y_4054_ = v___y_4028_;
                                    v___y_4055_ = v___y_4029_;
                                    v___y_4056_ = v___y_4030_;
                                    v___y_4057_ = v___y_4031_;
                                    v___y_4058_ = v___y_4032_;
                                    v___y_4059_ = v___y_4033_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___f_4049_);
                                    leanh::lean_dec_ref(v_value_4047_);
                                    leanh::lean_dec_ref(v_type_4046_);
                                    v_a_4080_ = leanh::lean_ctor_get(v___x_4078_, 0);
                                    v_isSharedCheck_4087_ =
                                        (!leanh::lean_is_exclusive(v___x_4078_)) as u8;
                                    if v_isSharedCheck_4087_ == 0 {
                                        v___x_4082_ = v___x_4078_;
                                        v_isShared_4083_ = v_isSharedCheck_4087_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4080_);
                                        leanh::lean_dec(v___x_4078_);
                                        v___x_4082_ = leanh::lean_box(0);
                                        v_isShared_4083_ = v_isSharedCheck_4087_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_declName_4045_);
                                v___x_4088_ = l_Lean_TSyntax_getId(v_name_4075_);
                                leanh::lean_dec(v_name_4075_);
                                v_name_4051_ = v___x_4088_;
                                v___y_4052_ = v___y_4026_;
                                v___y_4053_ = v___y_4027_;
                                v___y_4054_ = v___y_4028_;
                                v___y_4055_ = v___y_4029_;
                                v___y_4056_ = v___y_4030_;
                                v___y_4057_ = v___y_4031_;
                                v___y_4058_ = v___y_4032_;
                                v___y_4059_ = v___y_4033_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_hyps_4037_);
                        leanh::lean_dec_ref(v_00_u03c3s_4036_);
                        leanh::lean_dec(v_u_4035_);
                        leanh::lean_dec_ref(v_k_4025_);
                        leanh::lean_dec(v_ident_4024_);
                        v___x_4089_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__31,
                        );
                        v___x_4090_ = l_Lean_MessageData_ofExpr(v_target_4038_);
                        v___x_4091_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4091_, 0, v___x_4089_);
                        leanh::lean_ctor_set(v___x_4091_, 1, v___x_4090_);
                        v___x_4092_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v___x_4091_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
                        return v___x_4092_;
                    }
                } else {
                    v___x_4093_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
                        v_ident_4024_,
                        v___y_4032_,
                        v___y_4033_,
                    );
                    if leanh::lean_obj_tag(v___x_4093_) == 0 {
                        v_a_4094_ = leanh::lean_ctor_get(v___x_4093_, 0);
                        leanh::lean_inc(v_a_4094_);
                        leanh::lean_dec_ref_known(v___x_4093_, 1);
                        v_fst_4095_ = leanh::lean_ctor_get(v_a_4094_, 0);
                        leanh::lean_inc(v_fst_4095_);
                        v_snd_4096_ = leanh::lean_ctor_get(v_a_4094_, 1);
                        leanh::lean_inc(v_snd_4096_);
                        leanh::lean_dec(v_a_4094_);
                        v___x_4097_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_4033_);
                        v_a_4098_ = leanh::lean_ctor_get(v___x_4097_, 0);
                        leanh::lean_inc(v_a_4098_);
                        leanh::lean_dec_ref(v___x_4097_);
                        v___x_4099_ = l_Lean_Expr_appFn_x21(v_target_4038_);
                        v___x_4100_ = l_Lean_Expr_appFn_x21(v___x_4099_);
                        v___x_4101_ = l_Lean_Expr_appArg_x21(v___x_4100_);
                        leanh::lean_dec_ref(v___x_4100_);
                        v___x_4102_ = l_Lean_Expr_appArg_x21(v___x_4099_);
                        leanh::lean_dec_ref(v___x_4099_);
                        v_hyp_4103_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_hyp_4103_, 0, v_fst_4095_);
                        leanh::lean_ctor_set(v_hyp_4103_, 1, v_a_4098_);
                        leanh::lean_ctor_set(v_hyp_4103_, 2, v___x_4102_);
                        leanh::lean_inc_ref(v_hyp_4103_);
                        leanh::lean_inc_ref(v___x_4101_);
                        v___x_4104_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                            v_snd_4096_,
                            v___x_4101_,
                            v_hyp_4103_,
                            v___x_4044_,
                            v___y_4030_,
                            v___y_4031_,
                            v___y_4032_,
                            v___y_4033_,
                        );
                        if leanh::lean_obj_tag(v___x_4104_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4104_, 1);
                            v_H_4105_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v_hyp_4103_);
                            leanh::lean_inc_ref(v_H_4105_);
                            leanh::lean_inc_ref(v_hyps_4037_);
                            leanh::lean_inc_ref(v_00_u03c3s_4036_);
                            leanh::lean_inc(v_u_4035_);
                            v___x_4106_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                                v_u_4035_,
                                v_00_u03c3s_4036_,
                                v_hyps_4037_,
                                v_H_4105_,
                            );
                            v_fst_4107_ = leanh::lean_ctor_get(v___x_4106_, 0);
                            v_snd_4108_ = leanh::lean_ctor_get(v___x_4106_, 1);
                            v_isSharedCheck_4132_ =
                                (!leanh::lean_is_exclusive(v___x_4106_)) as u8;
                            if v_isSharedCheck_4132_ == 0 {
                                v___x_4110_ = v___x_4106_;
                                v_isShared_4111_ = v_isSharedCheck_4132_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4108_);
                                leanh::lean_inc(v_fst_4107_);
                                leanh::lean_dec(v___x_4106_);
                                v___x_4110_ = leanh::lean_box(0);
                                v_isShared_4111_ = v_isSharedCheck_4132_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_hyp_4103_, 3);
                            leanh::lean_dec_ref(v___x_4101_);
                            leanh::lean_del_object(v___x_4040_);
                            leanh::lean_dec_ref(v_target_4038_);
                            leanh::lean_dec_ref(v_hyps_4037_);
                            leanh::lean_dec_ref(v_00_u03c3s_4036_);
                            leanh::lean_dec(v_u_4035_);
                            leanh::lean_dec_ref(v_k_4025_);
                            v_a_4133_ = leanh::lean_ctor_get(v___x_4104_, 0);
                            v_isSharedCheck_4140_ =
                                (!leanh::lean_is_exclusive(v___x_4104_)) as u8;
                            if v_isSharedCheck_4140_ == 0 {
                                v___x_4135_ = v___x_4104_;
                                v_isShared_4136_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4133_);
                                leanh::lean_dec(v___x_4104_);
                                v___x_4135_ = leanh::lean_box(0);
                                v_isShared_4136_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_4040_);
                        leanh::lean_dec_ref(v_target_4038_);
                        leanh::lean_dec_ref(v_hyps_4037_);
                        leanh::lean_dec_ref(v_00_u03c3s_4036_);
                        leanh::lean_dec(v_u_4035_);
                        leanh::lean_dec_ref(v_k_4025_);
                        v_a_4141_ = leanh::lean_ctor_get(v___x_4093_, 0);
                        v_isSharedCheck_4148_ =
                            (!leanh::lean_is_exclusive(v___x_4093_)) as u8;
                        if v_isSharedCheck_4148_ == 0 {
                            v___x_4143_ = v___x_4093_;
                            v_isShared_4144_ = v_isSharedCheck_4148_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4141_);
                            leanh::lean_dec(v___x_4093_);
                            v___x_4143_ = leanh::lean_box(0);
                            v_isShared_4144_ = v_isSharedCheck_4148_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4060_ = 0;
                v___x_4061_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_4051_, v_type_4046_, v_value_4047_, v___f_4049_, v___x_4044_, v___x_4060_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
                return v___x_4061_;
            }
            3 => {
                if v_isShared_4069_ == 0 {
                    v___x_4071_ = v___x_4068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
                    v___x_4071_ = v_reuseFailAlloc_4072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4071_;
            }
            5 => {
                if v_isShared_4083_ == 0 {
                    v___x_4085_ = v___x_4082_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
                    v___x_4085_ = v_reuseFailAlloc_4086_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4085_;
            }
            7 => {
                v___x_4112_ = l_Lean_Expr_appArg_x21(v_target_4038_);
                leanh::lean_dec_ref(v_target_4038_);
                leanh::lean_inc_ref(v___x_4112_);
                leanh::lean_inc(v_fst_4107_);
                leanh::lean_inc(v_u_4035_);
                if v_isShared_4041_ == 0 {
                    leanh::lean_ctor_set(v___x_4040_, 3, v___x_4112_);
                    leanh::lean_ctor_set(v___x_4040_, 2, v_fst_4107_);
                    v___x_4114_ = v___x_4040_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_u_4035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_00_u03c3s_4036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 2, v_fst_4107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 3, v___x_4112_);
                    v___x_4114_ = v_reuseFailAlloc_4131_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc(v___y_4033_);
                leanh::lean_inc_ref(v___y_4032_);
                leanh::lean_inc(v___y_4031_);
                leanh::lean_inc_ref(v___y_4030_);
                leanh::lean_inc(v___y_4029_);
                leanh::lean_inc_ref(v___y_4028_);
                leanh::lean_inc(v___y_4027_);
                leanh::lean_inc_ref(v___y_4026_);
                v___x_4115_ = leanh::lean_apply_10(
                    v_k_4025_,
                    v___x_4114_,
                    v___y_4026_,
                    v___y_4027_,
                    v___y_4028_,
                    v___y_4029_,
                    v___y_4030_,
                    v___y_4031_,
                    v___y_4032_,
                    v___y_4033_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4115_) == 0 {
                    v_a_4116_ = leanh::lean_ctor_get(v___x_4115_, 0);
                    v_isSharedCheck_4130_ = (!leanh::lean_is_exclusive(v___x_4115_)) as u8;
                    if v_isSharedCheck_4130_ == 0 {
                        v___x_4118_ = v___x_4115_;
                        v_isShared_4119_ = v_isSharedCheck_4130_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4116_);
                        leanh::lean_dec(v___x_4115_);
                        v___x_4118_ = leanh::lean_box(0);
                        v_isShared_4119_ = v_isSharedCheck_4130_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4112_);
                    leanh::lean_del_object(v___x_4110_);
                    leanh::lean_dec(v_snd_4108_);
                    leanh::lean_dec(v_fst_4107_);
                    leanh::lean_dec_ref(v_H_4105_);
                    leanh::lean_dec_ref(v___x_4101_);
                    leanh::lean_dec_ref(v_hyps_4037_);
                    leanh::lean_dec(v_u_4035_);
                    return v___x_4115_;
                }
            }
            9 => {
                v___x_4120_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___closed__0;
                v___x_4121_ = leanh::lean_box(0);
                if v_isShared_4111_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4110_, 1);
                    leanh::lean_ctor_set(v___x_4110_, 1, v___x_4121_);
                    leanh::lean_ctor_set(v___x_4110_, 0, v_u_4035_);
                    v___x_4123_ = v___x_4110_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_u_4035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 1, v___x_4121_);
                    v___x_4123_ = v_reuseFailAlloc_4129_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_4124_ = l_Lean_mkConst(v___x_4120_, v___x_4123_);
                v_prf_4125_ = l_Lean_mkApp7(
                    v___x_4124_,
                    v___x_4101_,
                    v_fst_4107_,
                    v_hyps_4037_,
                    v_H_4105_,
                    v___x_4112_,
                    v_snd_4108_,
                    v_a_4116_,
                );
                if v_isShared_4119_ == 0 {
                    leanh::lean_ctor_set(v___x_4118_, 0, v_prf_4125_);
                    v___x_4127_ = v___x_4118_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_prf_4125_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4127_;
            }
            12 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4138_;
            }
            14 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4___boxed(
    mut v_goal_4150_: *mut leanh::LeanObject,
    mut v_ident_4151_: *mut leanh::LeanObject,
    mut v_k_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
    mut v___y_4159_: *mut leanh::LeanObject,
    mut v___y_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4162_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_goal_4150_, v_ident_4151_, v_k_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
    leanh::lean_dec(v___y_4160_);
    leanh::lean_dec_ref(v___y_4159_);
    leanh::lean_dec(v___y_4158_);
    leanh::lean_dec_ref(v___y_4157_);
    leanh::lean_dec(v___y_4156_);
    leanh::lean_dec_ref(v___y_4155_);
    leanh::lean_dec(v___y_4154_);
    leanh::lean_dec_ref(v___y_4153_);
    return v_res_4162_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(
    mut v___x_4163_: *mut leanh::LeanObject,
    mut v_snd_4164_: *mut leanh::LeanObject,
    mut v_ident_4165_: *mut leanh::LeanObject,
    mut v_fst_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4176_ = lean_st_mk_ref(v___x_4163_);
                leanh::lean_inc(v___x_4176_);
                v___f_4177_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    1,
                );
                leanh::lean_closure_set(v___f_4177_, 0, v___x_4176_);
                v___x_4178_ = l_Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4(v_snd_4164_, v_ident_4165_, v___f_4177_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
                if leanh::lean_obj_tag(v___x_4178_) == 0 {
                    v_a_4179_ = leanh::lean_ctor_get(v___x_4178_, 0);
                    leanh::lean_inc(v_a_4179_);
                    leanh::lean_dec_ref_known(v___x_4178_, 1);
                    v___x_4180_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(v_fst_4166_, v_a_4179_, v___y_4172_);
                    leanh::lean_dec_ref(v___x_4180_);
                    v___x_4181_ = lean_st_ref_get(v___x_4176_);
                    leanh::lean_dec(v___x_4176_);
                    v___x_4182_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_4181_,
                        v___y_4168_,
                        v___y_4171_,
                        v___y_4172_,
                        v___y_4173_,
                        v___y_4174_,
                    );
                    return v___x_4182_;
                } else {
                    leanh::lean_dec(v___x_4176_);
                    leanh::lean_dec(v_fst_4166_);
                    v_a_4183_ = leanh::lean_ctor_get(v___x_4178_, 0);
                    v_isSharedCheck_4190_ = (!leanh::lean_is_exclusive(v___x_4178_)) as u8;
                    if v_isSharedCheck_4190_ == 0 {
                        v___x_4185_ = v___x_4178_;
                        v_isShared_4186_ = v_isSharedCheck_4190_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4183_);
                        leanh::lean_dec(v___x_4178_);
                        v___x_4185_ = leanh::lean_box(0);
                        v_isShared_4186_ = v_isSharedCheck_4190_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4186_ == 0 {
                    v___x_4188_ = v___x_4185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed(
    mut v___x_4191_: *mut leanh::LeanObject,
    mut v_snd_4192_: *mut leanh::LeanObject,
    mut v_ident_4193_: *mut leanh::LeanObject,
    mut v_fst_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3(
        v___x_4191_,
        v_snd_4192_,
        v_ident_4193_,
        v_fst_4194_,
        v___y_4195_,
        v___y_4196_,
        v___y_4197_,
        v___y_4198_,
        v___y_4199_,
        v___y_4200_,
        v___y_4201_,
        v___y_4202_,
    );
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec_ref(v___y_4201_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v___y_4196_);
    leanh::lean_dec_ref(v___y_4195_);
    return v_res_4204_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(
    mut v_x_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_a_4213_: *mut leanh::LeanObject,
    mut v_a_4214_: *mut leanh::LeanObject,
    mut v_a_4215_: *mut leanh::LeanObject,
    mut v_a_4216_: *mut leanh::LeanObject,
    mut v_a_4217_: *mut leanh::LeanObject,
    mut v_a_4218_: *mut leanh::LeanObject,
    mut v_a_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: u8 = 0;
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ident_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4249_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ident_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: u8 = 0;
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4272_: u8 = 0;
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1;
                leanh::lean_inc(v_x_4211_);
                v___x_4222_ = l_Lean_Syntax_isOfKind(v_x_4211_, v___x_4221_);
                if v___x_4222_ == 0 {
                    leanh::lean_dec(v_x_4211_);
                    v___x_4223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                    return v___x_4223_;
                } else {
                    v___x_4224_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4225_ = l_Lean_Syntax_getArg(v_x_4211_, v___x_4224_);
                    leanh::lean_dec(v_x_4211_);
                    leanh::lean_inc(v___x_4225_);
                    v___x_4226_ = l_Lean_Syntax_matchesNull(v___x_4225_, v___x_4224_);
                    if v___x_4226_ == 0 {
                        leanh::lean_dec(v___x_4225_);
                        v___x_4227_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                        return v___x_4227_;
                    } else {
                        v___x_4228_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4229_ = l_Lean_Syntax_getArg(v___x_4225_, v___x_4228_);
                        leanh::lean_dec(v___x_4225_);
                        v___x_4230_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__3;
                        leanh::lean_inc(v___x_4229_);
                        v___x_4231_ = l_Lean_Syntax_isOfKind(v___x_4229_, v___x_4230_);
                        if v___x_4231_ == 0 {
                            v___x_4232_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___closed__1;
                            leanh::lean_inc(v___x_4229_);
                            v___x_4233_ = l_Lean_Syntax_isOfKind(v___x_4229_, v___x_4232_);
                            if v___x_4233_ == 0 {
                                leanh::lean_dec(v___x_4229_);
                                v___x_4234_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                                return v___x_4234_;
                            } else {
                                v_ident_4235_ = l_Lean_Syntax_getArg(v___x_4229_, v___x_4224_);
                                leanh::lean_dec(v___x_4229_);
                                v___x_4236_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                                leanh::lean_inc(v_ident_4235_);
                                v___x_4237_ = l_Lean_Syntax_isOfKind(v_ident_4235_, v___x_4236_);
                                if v___x_4237_ == 0 {
                                    leanh::lean_dec(v_ident_4235_);
                                    v___x_4238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                                    return v___x_4238_;
                                } else {
                                    v___x_4239_ =
                                        l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                                            v_a_4213_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_,
                                        );
                                    if leanh::lean_obj_tag(v___x_4239_) == 0 {
                                        v_a_4240_ = leanh::lean_ctor_get(v___x_4239_, 0);
                                        leanh::lean_inc(v_a_4240_);
                                        leanh::lean_dec_ref_known(v___x_4239_, 1);
                                        v_fst_4241_ = leanh::lean_ctor_get(v_a_4240_, 0);
                                        leanh::lean_inc_n(v_fst_4241_, 2);
                                        v_snd_4242_ = leanh::lean_ctor_get(v_a_4240_, 1);
                                        leanh::lean_inc(v_snd_4242_);
                                        leanh::lean_dec(v_a_4240_);
                                        v___x_4243_ = leanh::lean_box(0);
                                        v___f_4244_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__1___boxed as *mut core::ffi::c_void, 13, 4);
                                        leanh::lean_closure_set(v___f_4244_, 0, v___x_4243_);
                                        leanh::lean_closure_set(v___f_4244_, 1, v_snd_4242_);
                                        leanh::lean_closure_set(
                                            v___f_4244_,
                                            2,
                                            v_ident_4235_,
                                        );
                                        leanh::lean_closure_set(v___f_4244_, 3, v_fst_4241_);
                                        v___x_4245_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_4241_, v___f_4244_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
                                        return v___x_4245_;
                                    } else {
                                        leanh::lean_dec(v_ident_4235_);
                                        v_a_4246_ = leanh::lean_ctor_get(v___x_4239_, 0);
                                        v_isSharedCheck_4253_ =
                                            (!leanh::lean_is_exclusive(v___x_4239_)) as u8;
                                        if v_isSharedCheck_4253_ == 0 {
                                            v___x_4248_ = v___x_4239_;
                                            v_isShared_4249_ = v_isSharedCheck_4253_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4246_);
                                            leanh::lean_dec(v___x_4239_);
                                            v___x_4248_ = leanh::lean_box(0);
                                            v_isShared_4249_ = v_isSharedCheck_4253_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_4254_ = l_Lean_Syntax_getArg(v___x_4229_, v___x_4228_);
                            leanh::lean_dec(v___x_4229_);
                            v___x_4255_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__5;
                            leanh::lean_inc(v___x_4254_);
                            v___x_4256_ = l_Lean_Syntax_isOfKind(v___x_4254_, v___x_4255_);
                            if v___x_4256_ == 0 {
                                leanh::lean_dec(v___x_4254_);
                                v___x_4257_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                                return v___x_4257_;
                            } else {
                                v_ident_4258_ = l_Lean_Syntax_getArg(v___x_4254_, v___x_4228_);
                                leanh::lean_dec(v___x_4254_);
                                v___x_4259_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_mIntro___redArg___closed__27;
                                leanh::lean_inc(v_ident_4258_);
                                v___x_4260_ = l_Lean_Syntax_isOfKind(v_ident_4258_, v___x_4259_);
                                if v___x_4260_ == 0 {
                                    leanh::lean_dec(v_ident_4258_);
                                    v___x_4261_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__0___redArg();
                                    return v___x_4261_;
                                } else {
                                    v___x_4262_ =
                                        l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                                            v_a_4213_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_,
                                        );
                                    if leanh::lean_obj_tag(v___x_4262_) == 0 {
                                        v_a_4263_ = leanh::lean_ctor_get(v___x_4262_, 0);
                                        leanh::lean_inc(v_a_4263_);
                                        leanh::lean_dec_ref_known(v___x_4262_, 1);
                                        v_fst_4264_ = leanh::lean_ctor_get(v_a_4263_, 0);
                                        leanh::lean_inc_n(v_fst_4264_, 2);
                                        v_snd_4265_ = leanh::lean_ctor_get(v_a_4263_, 1);
                                        leanh::lean_inc(v_snd_4265_);
                                        leanh::lean_dec(v_a_4263_);
                                        v___x_4266_ = leanh::lean_box(0);
                                        v___f_4267_ = leanh::lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___lam__3___boxed as *mut core::ffi::c_void, 13, 4);
                                        leanh::lean_closure_set(v___f_4267_, 0, v___x_4266_);
                                        leanh::lean_closure_set(v___f_4267_, 1, v_snd_4265_);
                                        leanh::lean_closure_set(
                                            v___f_4267_,
                                            2,
                                            v_ident_4258_,
                                        );
                                        leanh::lean_closure_set(v___f_4267_, 3, v_fst_4264_);
                                        v___x_4268_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__3___redArg(v_fst_4264_, v___f_4267_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
                                        return v___x_4268_;
                                    } else {
                                        leanh::lean_dec(v_ident_4258_);
                                        v_a_4269_ = leanh::lean_ctor_get(v___x_4262_, 0);
                                        v_isSharedCheck_4276_ =
                                            (!leanh::lean_is_exclusive(v___x_4262_)) as u8;
                                        if v_isSharedCheck_4276_ == 0 {
                                            v___x_4271_ = v___x_4262_;
                                            v_isShared_4272_ = v_isSharedCheck_4276_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4269_);
                                            leanh::lean_dec(v___x_4262_);
                                            v___x_4271_ = leanh::lean_box(0);
                                            v_isShared_4272_ = v_isSharedCheck_4276_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4249_ == 0 {
                    v___x_4251_ = v___x_4248_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
                    v___x_4251_ = v_reuseFailAlloc_4252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4251_;
            }
            3 => {
                if v_isShared_4272_ == 0 {
                    v___x_4274_ = v___x_4271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
                    v___x_4274_ = v_reuseFailAlloc_4275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed(
    mut v_x_4277_: *mut leanh::LeanObject,
    mut v_a_4278_: *mut leanh::LeanObject,
    mut v_a_4279_: *mut leanh::LeanObject,
    mut v_a_4280_: *mut leanh::LeanObject,
    mut v_a_4281_: *mut leanh::LeanObject,
    mut v_a_4282_: *mut leanh::LeanObject,
    mut v_a_4283_: *mut leanh::LeanObject,
    mut v_a_4284_: *mut leanh::LeanObject,
    mut v_a_4285_: *mut leanh::LeanObject,
    mut v_a_4286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4287_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro(
        v_x_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_,
        v_a_4285_,
    );
    leanh::lean_dec(v_a_4285_);
    leanh::lean_dec_ref(v_a_4284_);
    leanh::lean_dec(v_a_4283_);
    leanh::lean_dec_ref(v_a_4282_);
    leanh::lean_dec(v_a_4281_);
    leanh::lean_dec_ref(v_a_4280_);
    leanh::lean_dec(v_a_4279_);
    leanh::lean_dec_ref(v_a_4278_);
    return v_res_4287_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(
    mut v_mvarId_4288_: *mut leanh::LeanObject,
    mut v_val_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
    mut v___y_4294_: *mut leanh::LeanObject,
    mut v___y_4295_: *mut leanh::LeanObject,
    mut v___y_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___redArg(
            v_mvarId_4288_,
            v_val_4289_,
            v___y_4295_,
        );
    return v___x_4299_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2___boxed(
    mut v_mvarId_4300_: *mut leanh::LeanObject,
    mut v_val_4301_: *mut leanh::LeanObject,
    mut v___y_4302_: *mut leanh::LeanObject,
    mut v___y_4303_: *mut leanh::LeanObject,
    mut v___y_4304_: *mut leanh::LeanObject,
    mut v___y_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4311_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2(
        v_mvarId_4300_,
        v_val_4301_,
        v___y_4302_,
        v___y_4303_,
        v___y_4304_,
        v___y_4305_,
        v___y_4306_,
        v___y_4307_,
        v___y_4308_,
        v___y_4309_,
    );
    leanh::lean_dec(v___y_4309_);
    leanh::lean_dec_ref(v___y_4308_);
    leanh::lean_dec(v___y_4307_);
    leanh::lean_dec_ref(v___y_4306_);
    leanh::lean_dec(v___y_4305_);
    leanh::lean_dec_ref(v___y_4304_);
    leanh::lean_dec(v___y_4303_);
    leanh::lean_dec_ref(v___y_4302_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(
    mut v_00_u03b1_4312_: *mut leanh::LeanObject,
    mut v_name_4313_: *mut leanh::LeanObject,
    mut v_type_4314_: *mut leanh::LeanObject,
    mut v_val_4315_: *mut leanh::LeanObject,
    mut v_k_4316_: *mut leanh::LeanObject,
    mut v_nondep_4317_: u8,
    mut v_kind_4318_: u8,
    mut v___y_4319_: *mut leanh::LeanObject,
    mut v___y_4320_: *mut leanh::LeanObject,
    mut v___y_4321_: *mut leanh::LeanObject,
    mut v___y_4322_: *mut leanh::LeanObject,
    mut v___y_4323_: *mut leanh::LeanObject,
    mut v___y_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4328_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___redArg(v_name_4313_, v_type_4314_, v_val_4315_, v_k_4316_, v_nondep_4317_, v_kind_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
    return v___x_4328_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7___boxed(
    mut v_00_u03b1_4329_: *mut leanh::LeanObject,
    mut v_name_4330_: *mut leanh::LeanObject,
    mut v_type_4331_: *mut leanh::LeanObject,
    mut v_val_4332_: *mut leanh::LeanObject,
    mut v_k_4333_: *mut leanh::LeanObject,
    mut v_nondep_4334_: *mut leanh::LeanObject,
    mut v_kind_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
    mut v___y_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_4345_: u8 = 0;
    let mut v_kind_boxed_4346_: u8 = 0;
    let mut v_res_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4345_ = (leanh::lean_unbox(v_nondep_4334_) as u8);
    v_kind_boxed_4346_ = (leanh::lean_unbox(v_kind_4335_) as u8);
    v_res_4347_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__7(v_00_u03b1_4329_, v_name_4330_, v_type_4331_, v_val_4332_, v_k_4333_, v_nondep_boxed_4345_, v_kind_boxed_4346_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
    leanh::lean_dec(v___y_4343_);
    leanh::lean_dec_ref(v___y_4342_);
    leanh::lean_dec(v___y_4341_);
    leanh::lean_dec_ref(v___y_4340_);
    leanh::lean_dec(v___y_4339_);
    leanh::lean_dec_ref(v___y_4338_);
    leanh::lean_dec(v___y_4337_);
    leanh::lean_dec_ref(v___y_4336_);
    return v_res_4347_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(
    mut v___y_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___redArg(v___y_4351_);
    return v___x_4353_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8___boxed(
    mut v___y_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4359_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mIntro___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__4_spec__8(v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_);
    leanh::lean_dec(v___y_4357_);
    leanh::lean_dec_ref(v___y_4356_);
    leanh::lean_dec(v___y_4355_);
    leanh::lean_dec_ref(v___y_4354_);
    return v_res_4359_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(
    mut v_00_u03b1_4360_: *mut leanh::LeanObject,
    mut v_msg_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___redArg(v_msg_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
    return v___x_4367_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1___boxed(
    mut v_00_u03b1_4368_: *mut leanh::LeanObject,
    mut v_msg_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
    mut v___y_4372_: *mut leanh::LeanObject,
    mut v___y_4373_: *mut leanh::LeanObject,
    mut v___y_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__1(v_00_u03b1_4368_, v_msg_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
    leanh::lean_dec(v___y_4373_);
    leanh::lean_dec_ref(v___y_4372_);
    leanh::lean_dec(v___y_4371_);
    leanh::lean_dec_ref(v___y_4370_);
    return v_res_4375_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(
    mut v_00_u03b1_4376_: *mut leanh::LeanObject,
    mut v_name_4377_: *mut leanh::LeanObject,
    mut v_bi_4378_: u8,
    mut v_type_4379_: *mut leanh::LeanObject,
    mut v_k_4380_: *mut leanh::LeanObject,
    mut v_kind_4381_: u8,
    mut v___y_4382_: *mut leanh::LeanObject,
    mut v___y_4383_: *mut leanh::LeanObject,
    mut v___y_4384_: *mut leanh::LeanObject,
    mut v___y_4385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___redArg(v_name_4377_, v_bi_4378_, v_type_4379_, v_k_4380_, v_kind_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
    return v___x_4387_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b1_4388_: *mut leanh::LeanObject,
    mut v_name_4389_: *mut leanh::LeanObject,
    mut v_bi_4390_: *mut leanh::LeanObject,
    mut v_type_4391_: *mut leanh::LeanObject,
    mut v_k_4392_: *mut leanh::LeanObject,
    mut v_kind_4393_: *mut leanh::LeanObject,
    mut v___y_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
    mut v___y_4398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4399_: u8 = 0;
    let mut v_kind_boxed_4400_: u8 = 0;
    let mut v_res_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4399_ = (leanh::lean_unbox(v_bi_4390_) as u8);
    v_kind_boxed_4400_ = (leanh::lean_unbox(v_kind_4393_) as u8);
    v_res_4401_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2_spec__5(v_00_u03b1_4388_, v_name_4389_, v_bi_boxed_4399_, v_type_4391_, v_k_4392_, v_kind_boxed_4400_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
    leanh::lean_dec(v___y_4397_);
    leanh::lean_dec_ref(v___y_4396_);
    leanh::lean_dec(v___y_4395_);
    leanh::lean_dec_ref(v___y_4394_);
    return v_res_4401_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(
    mut v_00_u03b1_4402_: *mut leanh::LeanObject,
    mut v_name_4403_: *mut leanh::LeanObject,
    mut v_type_4404_: *mut leanh::LeanObject,
    mut v_k_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
    mut v___y_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
    mut v___y_4409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___redArg(v_name_4403_, v_type_4404_, v_k_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
    return v___x_4411_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2___boxed(
    mut v_00_u03b1_4412_: *mut leanh::LeanObject,
    mut v_name_4413_: *mut leanh::LeanObject,
    mut v_type_4414_: *mut leanh::LeanObject,
    mut v_k_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
    mut v___y_4418_: *mut leanh::LeanObject,
    mut v___y_4419_: *mut leanh::LeanObject,
    mut v___y_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4421_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mIntroForall___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__1_spec__2(v_00_u03b1_4412_, v_name_4413_, v_type_4414_, v_k_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
    leanh::lean_dec(v___y_4419_);
    leanh::lean_dec_ref(v___y_4418_);
    leanh::lean_dec(v___y_4417_);
    leanh::lean_dec_ref(v___y_4416_);
    return v_res_4421_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4(
    mut v_00_u03b2_4422_: *mut leanh::LeanObject,
    mut v_x_4423_: *mut leanh::LeanObject,
    mut v_x_4424_: *mut leanh::LeanObject,
    mut v_x_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4___redArg(v_x_4423_, v_x_4424_, v_x_4425_);
    return v___x_4426_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(
    mut v_00_u03b2_4427_: *mut leanh::LeanObject,
    mut v_x_4428_: *mut leanh::LeanObject,
    mut v_x_4429_: usize,
    mut v_x_4430_: usize,
    mut v_x_4431_: *mut leanh::LeanObject,
    mut v_x_4432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___redArg(v_x_4428_, v_x_4429_, v_x_4430_, v_x_4431_, v_x_4432_);
    return v___x_4433_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_4434_: *mut leanh::LeanObject,
    mut v_x_4435_: *mut leanh::LeanObject,
    mut v_x_4436_: *mut leanh::LeanObject,
    mut v_x_4437_: *mut leanh::LeanObject,
    mut v_x_4438_: *mut leanh::LeanObject,
    mut v_x_4439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21870__boxed_4440_: usize = 0;
    let mut v_x_21871__boxed_4441_: usize = 0;
    let mut v_res_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21870__boxed_4440_ = leanh::lean_unbox_usize(v_x_4436_);
    leanh::lean_dec(v_x_4436_);
    v_x_21871__boxed_4441_ = leanh::lean_unbox_usize(v_x_4437_);
    leanh::lean_dec(v_x_4437_);
    v_res_4442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8(v_00_u03b2_4434_, v_x_4435_, v_x_21870__boxed_4440_, v_x_21871__boxed_4441_, v_x_4438_, v_x_4439_);
    return v_res_4442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12(
    mut v_00_u03b2_4443_: *mut leanh::LeanObject,
    mut v_n_4444_: *mut leanh::LeanObject,
    mut v_k_4445_: *mut leanh::LeanObject,
    mut v_v_4446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4447_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12___redArg(v_n_4444_, v_k_4445_, v_v_4446_);
    return v___x_4447_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(
    mut v_00_u03b2_4448_: *mut leanh::LeanObject,
    mut v_depth_4449_: usize,
    mut v_keys_4450_: *mut leanh::LeanObject,
    mut v_vals_4451_: *mut leanh::LeanObject,
    mut v_heq_4452_: *mut leanh::LeanObject,
    mut v_i_4453_: *mut leanh::LeanObject,
    mut v_entries_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___redArg(v_depth_4449_, v_keys_4450_, v_vals_4451_, v_i_4453_, v_entries_4454_);
    return v___x_4455_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13___boxed(
    mut v_00_u03b2_4456_: *mut leanh::LeanObject,
    mut v_depth_4457_: *mut leanh::LeanObject,
    mut v_keys_4458_: *mut leanh::LeanObject,
    mut v_vals_4459_: *mut leanh::LeanObject,
    mut v_heq_4460_: *mut leanh::LeanObject,
    mut v_i_4461_: *mut leanh::LeanObject,
    mut v_entries_4462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4463_: usize = 0;
    let mut v_res_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4463_ = leanh::lean_unbox_usize(v_depth_4457_);
    leanh::lean_dec(v_depth_4457_);
    v_res_4464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__13(v_00_u03b2_4456_, v_depth_boxed_4463_, v_keys_4458_, v_vals_4459_, v_heq_4460_, v_i_4461_, v_entries_4462_);
    leanh::lean_dec_ref(v_vals_4459_);
    leanh::lean_dec_ref(v_keys_4458_);
    return v_res_4464_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13(
    mut v_00_u03b2_4465_: *mut leanh::LeanObject,
    mut v_x_4466_: *mut leanh::LeanObject,
    mut v_x_4467_: *mut leanh::LeanObject,
    mut v_x_4468_: *mut leanh::LeanObject,
    mut v_x_4469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4470_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMIntro_spec__2_spec__4_spec__8_spec__12_spec__13___redArg(v_x_4466_, v_x_4467_, v_x_4468_, v_x_4469_);
    return v___x_4470_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1()
-> *mut leanh::LeanObject {
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4482_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4483_ = l_Lean_Elab_Tactic_Do_ProofMode___aux__Lean__Elab__Tactic__Do__ProofMode__Intro______macroRules__Lean__Parser__Tactic__mintro__1___closed__1;
    v___x_4484_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___closed__3;
    v___x_4485_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMIntro___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4486_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4482_,
        v___x_4483_,
        v___x_4484_,
        v___x_4485_,
    );
    return v___x_4486_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1___boxed(
    mut v_a_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4488_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
    return v_res_4488_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Intro_0__Lean_Elab_Tactic_Do_ProofMode_elabMIntro___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMIntro__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Intro(builtin);
}