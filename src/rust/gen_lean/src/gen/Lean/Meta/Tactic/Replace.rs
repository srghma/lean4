// Lean compiler output
// Module: Lean.Meta.Tactic.Replace
// Imports: Lean.Elab.InfoTree.Main Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Assert
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uset, lean_expr_equal,
    lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Basic::l_instMonadControlTOfPure___redArg;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_pure___boxed,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    initialize_Lean_Elab_InfoTree_Main, runtime_initialize_Lean_Elab_InfoTree_Main,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isLet, l_Lean_Expr_letBody_x21, l_Lean_Expr_letE___override,
    l_Lean_Expr_letName_x21, l_Lean_Expr_letType_x21, l_Lean_Expr_letValue_x21,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_get_x21, l_Lean_LocalContext_setType, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqMP,
    l_Lean_Meta_mkExpectedPropHint, l_Lean_Meta_mkExpectedTypeHint,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg, l_Lean_FVarId_getUserName___redArg, l_Lean_MVarId_getDecl,
    l_Lean_MVarId_setType___redArg, l_Lean_MVarId_withContext___redArg,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_withLocalInstancesImp___redArg,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_isTypeCorrect;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchEq_x3f, runtime_initialize_Lean_Meta_MatchUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::{
    initialize_Lean_Meta_Tactic_Assert, l_Lean_MVarId_assertAfter_x27,
    runtime_initialize_Lean_Meta_Tactic_Assert,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_introNCore;
use crate::r#gen::Lean::Meta::Tactic::Revert::{l_Lean_MVarId_revert, l_Lean_MVarId_revertFrom};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___boxed,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_setFVarType, l_Lean_instantiateMVarsCore,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value:
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
    m_data: [69, 113, 0],
};
static mut l_Lean_MVarId_replaceTargetEq___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 112, 114, 0],
};
static mut l_Lean_MVarId_replaceTargetEq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        503120329516084626 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_replaceTargetEq___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceTargetEq___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            114, 101, 112, 108, 97, 99, 101, 84, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lean_MVarId_replaceTargetEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceTargetEq___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8037993148428036496 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_replaceTargetEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceTargetDefEq___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [99, 104, 97, 110, 103, 101, 0],
    };
static mut l_Lean_MVarId_replaceTargetDefEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetDefEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceTargetDefEq___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_replaceTargetDefEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13755659578849458301 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_replaceTargetDefEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceTargetDefEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_replaceLocalDecl___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_replaceLocalDecl___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_replaceLocalDecl___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceLocalDecl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceLocalDecl___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceLocalDecl___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceLocalDecl___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceLocalDecl___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_replaceLocalDecl___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_replaceLocalDecl___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_replaceLocalDecl___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_change___lam__0___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [103, 105, 118, 101, 110, 32, 116, 121, 112, 101, 0],
    };
static mut l_Lean_MVarId_change___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_change___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_change___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_change___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_change___lam__0___closed__2_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
            97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 0,
        ],
    };
static mut l_Lean_MVarId_change___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_change___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_change___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_change___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_withReverted___redArg___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_MVarId_withReverted___redArg___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_withReverted___redArg___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114,
        121, 32, 116, 97, 114, 103, 101, 116, 0,
    ],
};
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_changeLocalDecl___lam__2___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_changeLocalDecl___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_changeLocalDecl___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            99, 104, 97, 110, 103, 101, 76, 111, 99, 97, 108, 68, 101, 99, 108, 0,
        ],
    };
static mut l_Lean_MVarId_changeLocalDecl___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_changeLocalDecl___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14543609422561288074 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_changeLocalDecl___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_changeLocalDecl___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_modifyTarget___closed__0_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [109, 111, 100, 105, 102, 121, 84, 97, 114, 103, 101, 116, 0],
    };
static mut l_Lean_MVarId_modifyTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_modifyTarget___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_modifyTarget___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_modifyTarget___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15068419438072449215 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_modifyTarget___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_modifyTarget___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value:
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
        109, 111, 100, 105, 102, 121, 84, 97, 114, 103, 101, 116, 69, 113, 76, 72, 83, 0,
    ],
};
static mut l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3388566883232191954 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2_value:
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
        101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clearValue___lam__0___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [99, 97, 110, 110, 111, 116, 32, 99, 108, 101, 97, 114, 32, 0],
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_clearValue___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clearValue___lam__0___closed__2_value: crate::leanh::LeanStringObject<45> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 45,
        m_capacity: 45,
        m_length: 44,
        m_data: [
            44, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 99, 111,
            110, 116, 101, 120, 116, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101, 32,
            99, 111, 114, 114, 101, 99, 116, 46, 0,
        ],
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_clearValue___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clearValue___lam__0___closed__4_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 96, 0],
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_clearValue___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clearValue___lam__0___closed__6_value: crate::leanh::LeanStringObject<29> =
    crate::leanh::LeanStringObject {
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
            96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 108, 111, 99, 97, 108, 32, 100, 101,
            102, 105, 110, 105, 116, 105, 111, 110, 46, 0,
        ],
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_clearValue___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_clearValue___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_clearValue___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 108, 101, 97, 114, 95, 118, 97, 108, 117, 101, 0],
    };
static mut l_Lean_MVarId_clearValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_clearValue___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_MVarId_clearValue___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8675278278543003851 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_clearValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_clearValue___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
    mut v_mvarId_2246_: *mut crate::leanh::LeanObject,
    mut v_x_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2261_: u8 = 0;
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2269_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2253_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2246_,
                    v_x_2247_,
                    v___y_2248_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                );
                if crate::leanh::lean_obj_tag(v___x_2253_) == 0 {
                    v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                    v_isSharedCheck_2261_ = (!crate::leanh::lean_is_exclusive(v___x_2253_)) as u8;
                    if v_isSharedCheck_2261_ == 0 {
                        v___x_2256_ = v___x_2253_;
                        v_isShared_2257_ = v_isSharedCheck_2261_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2254_);
                        crate::leanh::lean_dec(v___x_2253_);
                        v___x_2256_ = crate::leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2261_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2262_ = crate::leanh::lean_ctor_get(v___x_2253_, 0);
                    v_isSharedCheck_2269_ = (!crate::leanh::lean_is_exclusive(v___x_2253_)) as u8;
                    if v_isSharedCheck_2269_ == 0 {
                        v___x_2264_ = v___x_2253_;
                        v_isShared_2265_ = v_isSharedCheck_2269_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2262_);
                        crate::leanh::lean_dec(v___x_2253_);
                        v___x_2264_ = crate::leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2269_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2257_ == 0 {
                    v___x_2259_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
                    v___x_2259_ = v_reuseFailAlloc_2260_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2259_;
            }
            3 => {
                if v_isShared_2265_ == 0 {
                    v___x_2267_ = v___x_2264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
                    v___x_2267_ = v_reuseFailAlloc_2268_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg___boxed(
    mut v_mvarId_2270_: *mut crate::leanh::LeanObject,
    mut v_x_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_2270_,
        v_x_2271_,
        v___y_2272_,
        v___y_2273_,
        v___y_2274_,
        v___y_2275_,
    );
    crate::leanh::lean_dec(v___y_2275_);
    crate::leanh::lean_dec_ref(v___y_2274_);
    crate::leanh::lean_dec(v___y_2273_);
    crate::leanh::lean_dec_ref(v___y_2272_);
    return v_res_2277_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(
    mut v_00_u03b1_2278_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2279_: *mut crate::leanh::LeanObject,
    mut v_x_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_2279_,
        v_x_2280_,
        v___y_2281_,
        v___y_2282_,
        v___y_2283_,
        v___y_2284_,
    );
    return v___x_2286_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___boxed(
    mut v_00_u03b1_2287_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2288_: *mut crate::leanh::LeanObject,
    mut v_x_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1(
        v_00_u03b1_2287_,
        v_mvarId_2288_,
        v_x_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
    );
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_2296_: *mut crate::leanh::LeanObject,
    mut v_x_2297_: *mut crate::leanh::LeanObject,
    mut v_x_2298_: *mut crate::leanh::LeanObject,
    mut v_x_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2304_: u8 = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2300_ = crate::leanh::lean_ctor_get(v_x_2296_, 0);
                v_vs_2301_ = crate::leanh::lean_ctor_get(v_x_2296_, 1);
                v_isSharedCheck_2325_ = (!crate::leanh::lean_is_exclusive(v_x_2296_)) as u8;
                if v_isSharedCheck_2325_ == 0 {
                    v___x_2303_ = v_x_2296_;
                    v_isShared_2304_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2301_);
                    crate::leanh::lean_inc(v_ks_2300_);
                    crate::leanh::lean_dec(v_x_2296_);
                    v___x_2303_ = crate::leanh::lean_box(0);
                    v_isShared_2304_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2305_ = lean_array_get_size(v_ks_2300_);
                v___x_2306_ = lean_nat_dec_lt(v_x_2297_, v___x_2305_);
                if v___x_2306_ == 0 {
                    crate::leanh::lean_dec(v_x_2297_);
                    v___x_2307_ = lean_array_push(v_ks_2300_, v_x_2298_);
                    v___x_2308_ = lean_array_push(v_vs_2301_, v_x_2299_);
                    if v_isShared_2304_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2303_, 1, v___x_2308_);
                        crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2307_);
                        v___x_2310_ = v___x_2303_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2307_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2308_);
                        v___x_2310_ = v_reuseFailAlloc_2311_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2312_ = lean_array_fget_borrowed(v_ks_2300_, v_x_2297_);
                    v___x_2313_ = l_Lean_instBEqMVarId_beq(v_x_2298_, v_k_x27_2312_);
                    if v___x_2313_ == 0 {
                        if v_isShared_2304_ == 0 {
                            v___x_2315_ = v___x_2303_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2319_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_ks_2300_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_vs_2301_);
                            v___x_2315_ = v_reuseFailAlloc_2319_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2320_ = lean_array_fset(v_ks_2300_, v_x_2297_, v_x_2298_);
                        v___x_2321_ = lean_array_fset(v_vs_2301_, v_x_2297_, v_x_2299_);
                        crate::leanh::lean_dec(v_x_2297_);
                        if v_isShared_2304_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2303_, 1, v___x_2321_);
                            crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2320_);
                            v___x_2323_ = v___x_2303_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2324_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2320_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2321_);
                            v___x_2323_ = v_reuseFailAlloc_2324_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2310_;
            }
            3 => {
                v___x_2316_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2317_ = lean_nat_add(v_x_2297_, v___x_2316_);
                crate::leanh::lean_dec(v_x_2297_);
                v_x_2296_ = v___x_2315_;
                v_x_2297_ = v___x_2317_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_2326_: *mut crate::leanh::LeanObject,
    mut v_k_2327_: *mut crate::leanh::LeanObject,
    mut v_v_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2330_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_2326_, v___x_2329_, v_k_2327_, v_v_2328_);
    return v___x_2330_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2331_: usize = 0;
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: usize = 0;
    v___x_2331_ = 5usize;
    v___x_2332_ = 1usize;
    v___x_2333_ = lean_usize_shift_left(v___x_2332_, v___x_2331_);
    return v___x_2333_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: usize = 0;
    let mut v___x_2336_: usize = 0;
    v___x_2334_ = 1usize;
    v___x_2335_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_2336_ = lean_usize_sub(v___x_2335_, v___x_2334_);
    return v___x_2336_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2337_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(
    mut v_x_2338_: *mut crate::leanh::LeanObject,
    mut v_x_2339_: usize,
    mut v_x_2340_: usize,
    mut v_x_2341_: *mut crate::leanh::LeanObject,
    mut v_x_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: usize = 0;
    let mut v___x_2345_: usize = 0;
    let mut v___x_2346_: usize = 0;
    let mut v___x_2347_: usize = 0;
    let mut v_j_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v_v_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_node_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2379_: usize = 0;
    let mut v___x_2380_: usize = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut v_unused_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2393_: u8 = 0;
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2398_: u8 = 0;
    let mut v_ks_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: u8 = 0;
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2338_) == 0 {
                    v_es_2343_ = crate::leanh::lean_ctor_get(v_x_2338_, 0);
                    v___x_2344_ = 5usize;
                    v___x_2345_ = 1usize;
                    v___x_2346_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2347_ = lean_usize_land(v_x_2339_, v___x_2346_);
                    v_j_2348_ = lean_usize_to_nat(v___x_2347_);
                    v___x_2349_ = lean_array_get_size(v_es_2343_);
                    v___x_2350_ = lean_nat_dec_lt(v_j_2348_, v___x_2349_);
                    if v___x_2350_ == 0 {
                        crate::leanh::lean_dec(v_j_2348_);
                        crate::leanh::lean_dec(v_x_2342_);
                        crate::leanh::lean_dec(v_x_2341_);
                        return v_x_2338_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2343_);
                        v_isSharedCheck_2387_ = (!crate::leanh::lean_is_exclusive(v_x_2338_)) as u8;
                        if v_isSharedCheck_2387_ == 0 {
                            v_unused_2388_ = crate::leanh::lean_ctor_get(v_x_2338_, 0);
                            crate::leanh::lean_dec(v_unused_2388_);
                            v___x_2352_ = v_x_2338_;
                            v_isShared_2353_ = v_isSharedCheck_2387_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2338_);
                            v___x_2352_ = crate::leanh::lean_box(0);
                            v_isShared_2353_ = v_isSharedCheck_2387_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2389_ = crate::leanh::lean_ctor_get(v_x_2338_, 0);
                    v_vs_2390_ = crate::leanh::lean_ctor_get(v_x_2338_, 1);
                    v_isSharedCheck_2410_ = (!crate::leanh::lean_is_exclusive(v_x_2338_)) as u8;
                    if v_isSharedCheck_2410_ == 0 {
                        v___x_2392_ = v_x_2338_;
                        v_isShared_2393_ = v_isSharedCheck_2410_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2390_);
                        crate::leanh::lean_inc(v_ks_2389_);
                        crate::leanh::lean_dec(v_x_2338_);
                        v___x_2392_ = crate::leanh::lean_box(0);
                        v_isShared_2393_ = v_isSharedCheck_2410_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2354_ = lean_array_fget(v_es_2343_, v_j_2348_);
                v___x_2355_ = crate::leanh::lean_box(0);
                v_xs_x27_2356_ = lean_array_fset(v_es_2343_, v_j_2348_, v___x_2355_);
                match crate::leanh::lean_obj_tag(v_v_2354_) {
                    0 => {
                        v_key_2363_ = crate::leanh::lean_ctor_get(v_v_2354_, 0);
                        v_val_2364_ = crate::leanh::lean_ctor_get(v_v_2354_, 1);
                        v_isSharedCheck_2374_ = (!crate::leanh::lean_is_exclusive(v_v_2354_)) as u8;
                        if v_isSharedCheck_2374_ == 0 {
                            v___x_2366_ = v_v_2354_;
                            v_isShared_2367_ = v_isSharedCheck_2374_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2364_);
                            crate::leanh::lean_inc(v_key_2363_);
                            crate::leanh::lean_dec(v_v_2354_);
                            v___x_2366_ = crate::leanh::lean_box(0);
                            v_isShared_2367_ = v_isSharedCheck_2374_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2375_ = crate::leanh::lean_ctor_get(v_v_2354_, 0);
                        v_isSharedCheck_2385_ = (!crate::leanh::lean_is_exclusive(v_v_2354_)) as u8;
                        if v_isSharedCheck_2385_ == 0 {
                            v___x_2377_ = v_v_2354_;
                            v_isShared_2378_ = v_isSharedCheck_2385_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2375_);
                            crate::leanh::lean_dec(v_v_2354_);
                            v___x_2377_ = crate::leanh::lean_box(0);
                            v_isShared_2378_ = v_isSharedCheck_2385_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2386_, 0, v_x_2341_);
                        crate::leanh::lean_ctor_set(v___x_2386_, 1, v_x_2342_);
                        v___y_2358_ = v___x_2386_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2359_ = lean_array_fset(v_xs_x27_2356_, v_j_2348_, v___y_2358_);
                crate::leanh::lean_dec(v_j_2348_);
                if v_isShared_2353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2352_, 0, v___x_2359_);
                    v___x_2361_ = v___x_2352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2361_;
            }
            4 => {
                v___x_2368_ = l_Lean_instBEqMVarId_beq(v_x_2341_, v_key_2363_);
                if v___x_2368_ == 0 {
                    crate::leanh::lean_del_object(v___x_2366_);
                    v___x_2369_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2363_,
                        v_val_2364_,
                        v_x_2341_,
                        v_x_2342_,
                    );
                    v___x_2370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2370_, 0, v___x_2369_);
                    v___y_2358_ = v___x_2370_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2364_);
                    crate::leanh::lean_dec(v_key_2363_);
                    if v_isShared_2367_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2366_, 1, v_x_2342_);
                        crate::leanh::lean_ctor_set(v___x_2366_, 0, v_x_2341_);
                        v___x_2372_ = v___x_2366_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_x_2341_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_x_2342_);
                        v___x_2372_ = v_reuseFailAlloc_2373_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2358_ = v___x_2372_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2379_ = lean_usize_shift_right(v_x_2339_, v___x_2344_);
                v___x_2380_ = lean_usize_add(v_x_2340_, v___x_2345_);
                v___x_2381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_node_2375_, v___x_2379_, v___x_2380_, v_x_2341_, v_x_2342_);
                if v_isShared_2378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2381_);
                    v___x_2383_ = v___x_2377_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2358_ = v___x_2383_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2393_ == 0 {
                    v___x_2395_ = v___x_2392_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_ks_2389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_vs_2390_);
                    v___x_2395_ = v_reuseFailAlloc_2409_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2396_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v___x_2395_, v_x_2341_, v_x_2342_);
                v___x_2404_ = 7usize;
                v___x_2405_ = lean_usize_dec_le(v___x_2404_, v_x_2340_);
                if v___x_2405_ == 0 {
                    v___x_2406_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2396_);
                    v___x_2407_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2408_ = lean_nat_dec_lt(v___x_2406_, v___x_2407_);
                    crate::leanh::lean_dec(v___x_2406_);
                    v___y_2398_ = v___x_2408_;
                    state = 10;
                    continue;
                } else {
                    v___y_2398_ = v___x_2405_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2398_ == 0 {
                    v_ks_2399_ = crate::leanh::lean_ctor_get(v_newNode_2396_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2399_);
                    v_vs_2400_ = crate::leanh::lean_ctor_get(v_newNode_2396_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2400_);
                    crate::leanh::lean_dec_ref(v_newNode_2396_);
                    v___x_2401_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2402_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_2403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_x_2340_, v_ks_2399_, v_vs_2400_, v___x_2401_, v___x_2402_);
                    crate::leanh::lean_dec_ref(v_vs_2400_);
                    crate::leanh::lean_dec_ref(v_ks_2399_);
                    return v___x_2403_;
                } else {
                    return v_newNode_2396_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_2411_: usize,
    mut v_keys_2412_: *mut crate::leanh::LeanObject,
    mut v_vals_2413_: *mut crate::leanh::LeanObject,
    mut v_i_2414_: *mut crate::leanh::LeanObject,
    mut v_entries_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v_k_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: u64 = 0;
    let mut v_h_2421_: usize = 0;
    let mut v___x_2422_: usize = 0;
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: usize = 0;
    let mut v___x_2425_: usize = 0;
    let mut v___x_2426_: usize = 0;
    let mut v_h_2427_: usize = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2416_ = lean_array_get_size(v_keys_2412_);
                v___x_2417_ = lean_nat_dec_lt(v_i_2414_, v___x_2416_);
                if v___x_2417_ == 0 {
                    crate::leanh::lean_dec(v_i_2414_);
                    return v_entries_2415_;
                } else {
                    v_k_2418_ = lean_array_fget_borrowed(v_keys_2412_, v_i_2414_);
                    v_v_2419_ = lean_array_fget_borrowed(v_vals_2413_, v_i_2414_);
                    v___x_2420_ = l_Lean_instHashableMVarId_hash(v_k_2418_);
                    v_h_2421_ = lean_uint64_to_usize(v___x_2420_);
                    v___x_2422_ = 5usize;
                    v___x_2423_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2424_ = 1usize;
                    v___x_2425_ = lean_usize_sub(v_depth_2411_, v___x_2424_);
                    v___x_2426_ = lean_usize_mul(v___x_2422_, v___x_2425_);
                    v_h_2427_ = lean_usize_shift_right(v_h_2421_, v___x_2426_);
                    v___x_2428_ = lean_nat_add(v_i_2414_, v___x_2423_);
                    crate::leanh::lean_dec(v_i_2414_);
                    crate::leanh::lean_inc(v_v_2419_);
                    crate::leanh::lean_inc(v_k_2418_);
                    v___x_2429_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_entries_2415_, v_h_2427_, v_depth_2411_, v_k_2418_, v_v_2419_);
                    v_i_2414_ = v___x_2428_;
                    v_entries_2415_ = v___x_2429_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_2431_: *mut crate::leanh::LeanObject,
    mut v_keys_2432_: *mut crate::leanh::LeanObject,
    mut v_vals_2433_: *mut crate::leanh::LeanObject,
    mut v_i_2434_: *mut crate::leanh::LeanObject,
    mut v_entries_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2436_: usize = 0;
    let mut v_res_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2436_ = crate::leanh::lean_unbox_usize(v_depth_2431_);
    crate::leanh::lean_dec(v_depth_2431_);
    v_res_2437_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_2436_, v_keys_2432_, v_vals_2433_, v_i_2434_, v_entries_2435_);
    crate::leanh::lean_dec_ref(v_vals_2433_);
    crate::leanh::lean_dec_ref(v_keys_2432_);
    return v_res_2437_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_2438_: *mut crate::leanh::LeanObject,
    mut v_x_2439_: *mut crate::leanh::LeanObject,
    mut v_x_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
    mut v_x_2442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1698__boxed_2443_: usize = 0;
    let mut v_x_1699__boxed_2444_: usize = 0;
    let mut v_res_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1698__boxed_2443_ = crate::leanh::lean_unbox_usize(v_x_2439_);
    crate::leanh::lean_dec(v_x_2439_);
    v_x_1699__boxed_2444_ = crate::leanh::lean_unbox_usize(v_x_2440_);
    crate::leanh::lean_dec(v_x_2440_);
    v_res_2445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_2438_, v_x_1698__boxed_2443_, v_x_1699__boxed_2444_, v_x_2441_, v_x_2442_);
    return v_res_2445_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(
    mut v_x_2446_: *mut crate::leanh::LeanObject,
    mut v_x_2447_: *mut crate::leanh::LeanObject,
    mut v_x_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2449_: u64 = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = l_Lean_instHashableMVarId_hash(v_x_2447_);
    v___x_2450_ = lean_uint64_to_usize(v___x_2449_);
    v___x_2451_ = 1usize;
    v___x_2452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_2446_, v___x_2450_, v___x_2451_, v_x_2447_, v_x_2448_);
    return v___x_2452_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(
    mut v_mvarId_2453_: *mut crate::leanh::LeanObject,
    mut v_val_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2465_: u8 = 0;
    let mut v_depth_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2457_ = lean_st_ref_take(v___y_2455_);
                v_mctx_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                v_cache_2459_ = crate::leanh::lean_ctor_get(v___x_2457_, 1);
                v_zetaDeltaFVarIds_2460_ = crate::leanh::lean_ctor_get(v___x_2457_, 2);
                v_postponed_2461_ = crate::leanh::lean_ctor_get(v___x_2457_, 3);
                v_diag_2462_ = crate::leanh::lean_ctor_get(v___x_2457_, 4);
                v_isSharedCheck_2490_ = (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                if v_isSharedCheck_2490_ == 0 {
                    v___x_2464_ = v___x_2457_;
                    v_isShared_2465_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2462_);
                    crate::leanh::lean_inc(v_postponed_2461_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2460_);
                    crate::leanh::lean_inc(v_cache_2459_);
                    crate::leanh::lean_inc(v_mctx_2458_);
                    crate::leanh::lean_dec(v___x_2457_);
                    v___x_2464_ = crate::leanh::lean_box(0);
                    v_isShared_2465_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2466_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 0);
                v_levelAssignDepth_2467_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 1);
                v_lmvarCounter_2468_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 2);
                v_mvarCounter_2469_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 3);
                v_lDecls_2470_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 4);
                v_decls_2471_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 5);
                v_userNames_2472_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 6);
                v_lAssignment_2473_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 7);
                v_eAssignment_2474_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 8);
                v_dAssignment_2475_ = crate::leanh::lean_ctor_get(v_mctx_2458_, 9);
                v_isSharedCheck_2489_ = (!crate::leanh::lean_is_exclusive(v_mctx_2458_)) as u8;
                if v_isSharedCheck_2489_ == 0 {
                    v___x_2477_ = v_mctx_2458_;
                    v_isShared_2478_ = v_isSharedCheck_2489_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2475_);
                    crate::leanh::lean_inc(v_eAssignment_2474_);
                    crate::leanh::lean_inc(v_lAssignment_2473_);
                    crate::leanh::lean_inc(v_userNames_2472_);
                    crate::leanh::lean_inc(v_decls_2471_);
                    crate::leanh::lean_inc(v_lDecls_2470_);
                    crate::leanh::lean_inc(v_mvarCounter_2469_);
                    crate::leanh::lean_inc(v_lmvarCounter_2468_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2467_);
                    crate::leanh::lean_inc(v_depth_2466_);
                    crate::leanh::lean_dec(v_mctx_2458_);
                    v___x_2477_ = crate::leanh::lean_box(0);
                    v_isShared_2478_ = v_isSharedCheck_2489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2479_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_eAssignment_2474_, v_mvarId_2453_, v_val_2454_);
                if v_isShared_2478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2477_, 8, v___x_2479_);
                    v___x_2481_ = v___x_2477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2488_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_depth_2466_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2488_,
                        1,
                        v_levelAssignDepth_2467_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_lmvarCounter_2468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_mvarCounter_2469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_lDecls_2470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 5, v_decls_2471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_userNames_2472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_lAssignment_2473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 8, v___x_2479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2488_, 9, v_dAssignment_2475_);
                    v___x_2481_ = v_reuseFailAlloc_2488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2464_, 0, v___x_2481_);
                    v___x_2483_ = v___x_2464_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_cache_2459_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2487_,
                        2,
                        v_zetaDeltaFVarIds_2460_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_postponed_2461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_diag_2462_);
                    v___x_2483_ = v_reuseFailAlloc_2487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2484_ = lean_st_ref_set(v___y_2455_, v___x_2483_);
                v___x_2485_ = crate::leanh::lean_box(0);
                v___x_2486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2485_);
                return v___x_2486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg___boxed(
    mut v_mvarId_2491_: *mut crate::leanh::LeanObject,
    mut v_val_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(
        v_mvarId_2491_,
        v_val_2492_,
        v___y_2493_,
    );
    crate::leanh::lean_dec(v___y_2493_);
    return v_res_2495_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetEq___lam__0(
    mut v_mvarId_2501_: *mut crate::leanh::LeanObject,
    mut v___x_2502_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2503_: *mut crate::leanh::LeanObject,
    mut v_eqProof_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
    mut v___y_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v_unused_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_a_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2566_: u8 = 0;
    let mut v_a_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v_a_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2578_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2586_: u8 = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2501_);
                v___x_2510_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2501_,
                    v___x_2502_,
                    v___y_2505_,
                    v___y_2506_,
                    v___y_2507_,
                    v___y_2508_,
                );
                if crate::leanh::lean_obj_tag(v___x_2510_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2510_, 1);
                    crate::leanh::lean_inc(v_mvarId_2501_);
                    v___x_2511_ = l_Lean_MVarId_getTag(
                        v_mvarId_2501_,
                        v___y_2505_,
                        v___y_2506_,
                        v___y_2507_,
                        v___y_2508_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2511_) == 0 {
                        v_a_2512_ = crate::leanh::lean_ctor_get(v___x_2511_, 0);
                        crate::leanh::lean_inc(v_a_2512_);
                        crate::leanh::lean_dec_ref_known(v___x_2511_, 1);
                        crate::leanh::lean_inc_ref(v_targetNew_2503_);
                        v___x_2513_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_targetNew_2503_,
                            v_a_2512_,
                            v___y_2505_,
                            v___y_2506_,
                            v___y_2507_,
                            v___y_2508_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2513_) == 0 {
                            v_a_2514_ = crate::leanh::lean_ctor_get(v___x_2513_, 0);
                            crate::leanh::lean_inc(v_a_2514_);
                            crate::leanh::lean_dec_ref_known(v___x_2513_, 1);
                            crate::leanh::lean_inc(v_mvarId_2501_);
                            v___x_2515_ = l_Lean_MVarId_getType(
                                v_mvarId_2501_,
                                v___y_2505_,
                                v___y_2506_,
                                v___y_2507_,
                                v___y_2508_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2515_) == 0 {
                                v_a_2516_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                                crate::leanh::lean_inc_n(v_a_2516_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2515_, 1);
                                v___x_2517_ = l_Lean_Meta_getLevel(
                                    v_a_2516_,
                                    v___y_2505_,
                                    v___y_2506_,
                                    v___y_2507_,
                                    v___y_2508_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2517_) == 0 {
                                    v_a_2518_ = crate::leanh::lean_ctor_get(v___x_2517_, 0);
                                    crate::leanh::lean_inc(v_a_2518_);
                                    crate::leanh::lean_dec_ref_known(v___x_2517_, 1);
                                    crate::leanh::lean_inc_ref(v_targetNew_2503_);
                                    crate::leanh::lean_inc(v_a_2516_);
                                    v___x_2519_ = l_Lean_Meta_mkEq(
                                        v_a_2516_,
                                        v_targetNew_2503_,
                                        v___y_2505_,
                                        v___y_2506_,
                                        v___y_2507_,
                                        v___y_2508_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2519_) == 0 {
                                        v_a_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                        crate::leanh::lean_inc(v_a_2520_);
                                        crate::leanh::lean_dec_ref_known(v___x_2519_, 1);
                                        v___x_2521_ = l_Lean_Meta_mkExpectedPropHint(
                                            v_eqProof_2504_,
                                            v_a_2520_,
                                        );
                                        v___x_2522_ =
                                            l_Lean_MVarId_replaceTargetEq___lam__0___closed__2;
                                        v___x_2523_ = crate::leanh::lean_box(0);
                                        v___x_2524_ =
                                            crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2524_, 0, v_a_2518_);
                                        crate::leanh::lean_ctor_set(v___x_2524_, 1, v___x_2523_);
                                        v___x_2525_ = l_Lean_mkConst(v___x_2522_, v___x_2524_);
                                        v___x_2526_ = crate::leanh::lean_unsigned_to_nat(4);
                                        v___x_2527_ =
                                            lean_mk_empty_array_with_capacity(v___x_2526_);
                                        v___x_2528_ = lean_array_push(v___x_2527_, v_a_2516_);
                                        v___x_2529_ =
                                            lean_array_push(v___x_2528_, v_targetNew_2503_);
                                        v___x_2530_ = lean_array_push(v___x_2529_, v___x_2521_);
                                        crate::leanh::lean_inc(v_a_2514_);
                                        v___x_2531_ = lean_array_push(v___x_2530_, v_a_2514_);
                                        v___x_2532_ = l_Lean_mkAppN(v___x_2525_, v___x_2531_);
                                        crate::leanh::lean_dec_ref(v___x_2531_);
                                        v___x_2533_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_2501_, v___x_2532_, v___y_2506_);
                                        v_isSharedCheck_2541_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2533_)) as u8;
                                        if v_isSharedCheck_2541_ == 0 {
                                            v_unused_2542_ =
                                                crate::leanh::lean_ctor_get(v___x_2533_, 0);
                                            crate::leanh::lean_dec(v_unused_2542_);
                                            v___x_2535_ = v___x_2533_;
                                            v_isShared_2536_ = v_isSharedCheck_2541_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2533_);
                                            v___x_2535_ = crate::leanh::lean_box(0);
                                            v_isShared_2536_ = v_isSharedCheck_2541_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2518_);
                                        crate::leanh::lean_dec(v_a_2516_);
                                        crate::leanh::lean_dec(v_a_2514_);
                                        crate::leanh::lean_dec_ref(v_eqProof_2504_);
                                        crate::leanh::lean_dec_ref(v_targetNew_2503_);
                                        crate::leanh::lean_dec(v_mvarId_2501_);
                                        v_a_2543_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                        v_isSharedCheck_2550_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2519_)) as u8;
                                        if v_isSharedCheck_2550_ == 0 {
                                            v___x_2545_ = v___x_2519_;
                                            v_isShared_2546_ = v_isSharedCheck_2550_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2543_);
                                            crate::leanh::lean_dec(v___x_2519_);
                                            v___x_2545_ = crate::leanh::lean_box(0);
                                            v_isShared_2546_ = v_isSharedCheck_2550_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2516_);
                                    crate::leanh::lean_dec(v_a_2514_);
                                    crate::leanh::lean_dec_ref(v_eqProof_2504_);
                                    crate::leanh::lean_dec_ref(v_targetNew_2503_);
                                    crate::leanh::lean_dec(v_mvarId_2501_);
                                    v_a_2551_ = crate::leanh::lean_ctor_get(v___x_2517_, 0);
                                    v_isSharedCheck_2558_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2517_)) as u8;
                                    if v_isSharedCheck_2558_ == 0 {
                                        v___x_2553_ = v___x_2517_;
                                        v_isShared_2554_ = v_isSharedCheck_2558_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2551_);
                                        crate::leanh::lean_dec(v___x_2517_);
                                        v___x_2553_ = crate::leanh::lean_box(0);
                                        v_isShared_2554_ = v_isSharedCheck_2558_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2514_);
                                crate::leanh::lean_dec_ref(v_eqProof_2504_);
                                crate::leanh::lean_dec_ref(v_targetNew_2503_);
                                crate::leanh::lean_dec(v_mvarId_2501_);
                                v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                                v_isSharedCheck_2566_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2515_)) as u8;
                                if v_isSharedCheck_2566_ == 0 {
                                    v___x_2561_ = v___x_2515_;
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2559_);
                                    crate::leanh::lean_dec(v___x_2515_);
                                    v___x_2561_ = crate::leanh::lean_box(0);
                                    v_isShared_2562_ = v_isSharedCheck_2566_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_eqProof_2504_);
                            crate::leanh::lean_dec_ref(v_targetNew_2503_);
                            crate::leanh::lean_dec(v_mvarId_2501_);
                            v_a_2567_ = crate::leanh::lean_ctor_get(v___x_2513_, 0);
                            v_isSharedCheck_2574_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2513_)) as u8;
                            if v_isSharedCheck_2574_ == 0 {
                                v___x_2569_ = v___x_2513_;
                                v_isShared_2570_ = v_isSharedCheck_2574_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2567_);
                                crate::leanh::lean_dec(v___x_2513_);
                                v___x_2569_ = crate::leanh::lean_box(0);
                                v_isShared_2570_ = v_isSharedCheck_2574_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_eqProof_2504_);
                        crate::leanh::lean_dec_ref(v_targetNew_2503_);
                        crate::leanh::lean_dec(v_mvarId_2501_);
                        v_a_2575_ = crate::leanh::lean_ctor_get(v___x_2511_, 0);
                        v_isSharedCheck_2582_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2511_)) as u8;
                        if v_isSharedCheck_2582_ == 0 {
                            v___x_2577_ = v___x_2511_;
                            v_isShared_2578_ = v_isSharedCheck_2582_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2575_);
                            crate::leanh::lean_dec(v___x_2511_);
                            v___x_2577_ = crate::leanh::lean_box(0);
                            v_isShared_2578_ = v_isSharedCheck_2582_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_eqProof_2504_);
                    crate::leanh::lean_dec_ref(v_targetNew_2503_);
                    crate::leanh::lean_dec(v_mvarId_2501_);
                    v_a_2583_ = crate::leanh::lean_ctor_get(v___x_2510_, 0);
                    v_isSharedCheck_2590_ = (!crate::leanh::lean_is_exclusive(v___x_2510_)) as u8;
                    if v_isSharedCheck_2590_ == 0 {
                        v___x_2585_ = v___x_2510_;
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2583_);
                        crate::leanh::lean_dec(v___x_2510_);
                        v___x_2585_ = crate::leanh::lean_box(0);
                        v_isShared_2586_ = v_isSharedCheck_2590_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2537_ = l_Lean_Expr_mvarId_x21(v_a_2514_);
                crate::leanh::lean_dec(v_a_2514_);
                if v_isShared_2536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2537_);
                    v___x_2539_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2539_;
            }
            3 => {
                if v_isShared_2546_ == 0 {
                    v___x_2548_ = v___x_2545_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
                    v___x_2548_ = v_reuseFailAlloc_2549_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2548_;
            }
            5 => {
                if v_isShared_2554_ == 0 {
                    v___x_2556_ = v___x_2553_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
                    v___x_2556_ = v_reuseFailAlloc_2557_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2556_;
            }
            7 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2565_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2564_;
            }
            9 => {
                if v_isShared_2570_ == 0 {
                    v___x_2572_ = v___x_2569_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
                    v___x_2572_ = v_reuseFailAlloc_2573_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2572_;
            }
            11 => {
                if v_isShared_2578_ == 0 {
                    v___x_2580_ = v___x_2577_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
                    v___x_2580_ = v_reuseFailAlloc_2581_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2580_;
            }
            13 => {
                if v_isShared_2586_ == 0 {
                    v___x_2588_ = v___x_2585_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
                    v___x_2588_ = v_reuseFailAlloc_2589_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceTargetEq___lam__0___boxed(
    mut v_mvarId_2591_: *mut crate::leanh::LeanObject,
    mut v___x_2592_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2593_: *mut crate::leanh::LeanObject,
    mut v_eqProof_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2600_ = l_Lean_MVarId_replaceTargetEq___lam__0(
        v_mvarId_2591_,
        v___x_2592_,
        v_targetNew_2593_,
        v_eqProof_2594_,
        v___y_2595_,
        v___y_2596_,
        v___y_2597_,
        v___y_2598_,
    );
    crate::leanh::lean_dec(v___y_2598_);
    crate::leanh::lean_dec_ref(v___y_2597_);
    crate::leanh::lean_dec(v___y_2596_);
    crate::leanh::lean_dec_ref(v___y_2595_);
    return v_res_2600_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetEq(
    mut v_mvarId_2604_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2605_: *mut crate::leanh::LeanObject,
    mut v_eqProof_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Lean_MVarId_replaceTargetEq___closed__1;
    crate::leanh::lean_inc(v_mvarId_2604_);
    v___f_2613_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_replaceTargetEq___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2613_, 0, v_mvarId_2604_);
    crate::leanh::lean_closure_set(v___f_2613_, 1, v___x_2612_);
    crate::leanh::lean_closure_set(v___f_2613_, 2, v_targetNew_2605_);
    crate::leanh::lean_closure_set(v___f_2613_, 3, v_eqProof_2606_);
    v___x_2614_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_2604_,
        v___f_2613_,
        v_a_2607_,
        v_a_2608_,
        v_a_2609_,
        v_a_2610_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetEq___boxed(
    mut v_mvarId_2615_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2616_: *mut crate::leanh::LeanObject,
    mut v_eqProof_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Lean_MVarId_replaceTargetEq(
        v_mvarId_2615_,
        v_targetNew_2616_,
        v_eqProof_2617_,
        v_a_2618_,
        v_a_2619_,
        v_a_2620_,
        v_a_2621_,
    );
    crate::leanh::lean_dec(v_a_2621_);
    crate::leanh::lean_dec_ref(v_a_2620_);
    crate::leanh::lean_dec(v_a_2619_);
    crate::leanh::lean_dec_ref(v_a_2618_);
    return v_res_2623_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(
    mut v_mvarId_2624_: *mut crate::leanh::LeanObject,
    mut v_val_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(
        v_mvarId_2624_,
        v_val_2625_,
        v___y_2627_,
    );
    return v___x_2631_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___boxed(
    mut v_mvarId_2632_: *mut crate::leanh::LeanObject,
    mut v_val_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0(
        v_mvarId_2632_,
        v_val_2633_,
        v___y_2634_,
        v___y_2635_,
        v___y_2636_,
        v___y_2637_,
    );
    crate::leanh::lean_dec(v___y_2637_);
    crate::leanh::lean_dec_ref(v___y_2636_);
    crate::leanh::lean_dec(v___y_2635_);
    crate::leanh::lean_dec_ref(v___y_2634_);
    return v_res_2639_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0(
    mut v_00_u03b2_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
    mut v_x_2642_: *mut crate::leanh::LeanObject,
    mut v_x_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2644_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0___redArg(v_x_2641_, v_x_2642_, v_x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2645_: *mut crate::leanh::LeanObject,
    mut v_x_2646_: *mut crate::leanh::LeanObject,
    mut v_x_2647_: usize,
    mut v_x_2648_: usize,
    mut v_x_2649_: *mut crate::leanh::LeanObject,
    mut v_x_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2651_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___redArg(v_x_2646_, v_x_2647_, v_x_2648_, v_x_2649_, v_x_2650_);
    return v___x_2651_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2652_: *mut crate::leanh::LeanObject,
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v_x_2654_: *mut crate::leanh::LeanObject,
    mut v_x_2655_: *mut crate::leanh::LeanObject,
    mut v_x_2656_: *mut crate::leanh::LeanObject,
    mut v_x_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2159__boxed_2658_: usize = 0;
    let mut v_x_2160__boxed_2659_: usize = 0;
    let mut v_res_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2159__boxed_2658_ = crate::leanh::lean_unbox_usize(v_x_2654_);
    crate::leanh::lean_dec(v_x_2654_);
    v_x_2160__boxed_2659_ = crate::leanh::lean_unbox_usize(v_x_2655_);
    crate::leanh::lean_dec(v_x_2655_);
    v_res_2660_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2(v_00_u03b2_2652_, v_x_2653_, v_x_2159__boxed_2658_, v_x_2160__boxed_2659_, v_x_2656_, v_x_2657_);
    return v_res_2660_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_2661_: *mut crate::leanh::LeanObject,
    mut v_n_2662_: *mut crate::leanh::LeanObject,
    mut v_k_2663_: *mut crate::leanh::LeanObject,
    mut v_v_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2665_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3___redArg(v_n_2662_, v_k_2663_, v_v_2664_);
    return v___x_2665_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_2666_: *mut crate::leanh::LeanObject,
    mut v_depth_2667_: usize,
    mut v_keys_2668_: *mut crate::leanh::LeanObject,
    mut v_vals_2669_: *mut crate::leanh::LeanObject,
    mut v_heq_2670_: *mut crate::leanh::LeanObject,
    mut v_i_2671_: *mut crate::leanh::LeanObject,
    mut v_entries_2672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2673_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_2667_, v_keys_2668_, v_vals_2669_, v_i_2671_, v_entries_2672_);
    return v___x_2673_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_2674_: *mut crate::leanh::LeanObject,
    mut v_depth_2675_: *mut crate::leanh::LeanObject,
    mut v_keys_2676_: *mut crate::leanh::LeanObject,
    mut v_vals_2677_: *mut crate::leanh::LeanObject,
    mut v_heq_2678_: *mut crate::leanh::LeanObject,
    mut v_i_2679_: *mut crate::leanh::LeanObject,
    mut v_entries_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2681_: usize = 0;
    let mut v_res_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2681_ = crate::leanh::lean_unbox_usize(v_depth_2675_);
    crate::leanh::lean_dec(v_depth_2675_);
    v_res_2682_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_2674_, v_depth_boxed_2681_, v_keys_2676_, v_vals_2677_, v_heq_2678_, v_i_2679_, v_entries_2680_);
    crate::leanh::lean_dec_ref(v_vals_2677_);
    crate::leanh::lean_dec_ref(v_keys_2676_);
    return v_res_2682_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2683_: *mut crate::leanh::LeanObject,
    mut v_x_2684_: *mut crate::leanh::LeanObject,
    mut v_x_2685_: *mut crate::leanh::LeanObject,
    mut v_x_2686_: *mut crate::leanh::LeanObject,
    mut v_x_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_2684_, v_x_2685_, v_x_2686_, v_x_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(
    mut v_e_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2712_: u8 = 0;
    let mut v_unused_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2692_ = l_Lean_Expr_hasMVar(v_e_2689_);
                if v___x_2692_ == 0 {
                    v___x_2693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2693_, 0, v_e_2689_);
                    return v___x_2693_;
                } else {
                    v___x_2694_ = lean_st_ref_get(v___y_2690_);
                    v_mctx_2695_ = crate::leanh::lean_ctor_get(v___x_2694_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2695_);
                    crate::leanh::lean_dec(v___x_2694_);
                    v___x_2696_ = l_Lean_instantiateMVarsCore(v_mctx_2695_, v_e_2689_);
                    v_fst_2697_ = crate::leanh::lean_ctor_get(v___x_2696_, 0);
                    crate::leanh::lean_inc(v_fst_2697_);
                    v_snd_2698_ = crate::leanh::lean_ctor_get(v___x_2696_, 1);
                    crate::leanh::lean_inc(v_snd_2698_);
                    crate::leanh::lean_dec_ref(v___x_2696_);
                    v___x_2699_ = lean_st_ref_take(v___y_2690_);
                    v_cache_2700_ = crate::leanh::lean_ctor_get(v___x_2699_, 1);
                    v_zetaDeltaFVarIds_2701_ = crate::leanh::lean_ctor_get(v___x_2699_, 2);
                    v_postponed_2702_ = crate::leanh::lean_ctor_get(v___x_2699_, 3);
                    v_diag_2703_ = crate::leanh::lean_ctor_get(v___x_2699_, 4);
                    v_isSharedCheck_2712_ = (!crate::leanh::lean_is_exclusive(v___x_2699_)) as u8;
                    if v_isSharedCheck_2712_ == 0 {
                        v_unused_2713_ = crate::leanh::lean_ctor_get(v___x_2699_, 0);
                        crate::leanh::lean_dec(v_unused_2713_);
                        v___x_2705_ = v___x_2699_;
                        v_isShared_2706_ = v_isSharedCheck_2712_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2703_);
                        crate::leanh::lean_inc(v_postponed_2702_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2701_);
                        crate::leanh::lean_inc(v_cache_2700_);
                        crate::leanh::lean_dec(v___x_2699_);
                        v___x_2705_ = crate::leanh::lean_box(0);
                        v_isShared_2706_ = v_isSharedCheck_2712_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2705_, 0, v_snd_2698_);
                    v___x_2708_ = v___x_2705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2711_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_snd_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_cache_2700_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2711_,
                        2,
                        v_zetaDeltaFVarIds_2701_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_postponed_2702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_diag_2703_);
                    v___x_2708_ = v_reuseFailAlloc_2711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2709_ = lean_st_ref_set(v___y_2690_, v___x_2708_);
                v___x_2710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2710_, 0, v_fst_2697_);
                return v___x_2710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg___boxed(
    mut v_e_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2717_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(
        v_e_2714_,
        v___y_2715_,
    );
    crate::leanh::lean_dec(v___y_2715_);
    return v_res_2717_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(
    mut v_e_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2724_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(
        v_e_2718_,
        v___y_2720_,
    );
    return v___x_2724_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___boxed(
    mut v_e_2725_: *mut crate::leanh::LeanObject,
    mut v___y_2726_: *mut crate::leanh::LeanObject,
    mut v___y_2727_: *mut crate::leanh::LeanObject,
    mut v___y_2728_: *mut crate::leanh::LeanObject,
    mut v___y_2729_: *mut crate::leanh::LeanObject,
    mut v___y_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2731_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0(
        v_e_2725_,
        v___y_2726_,
        v___y_2727_,
        v___y_2728_,
        v___y_2729_,
    );
    crate::leanh::lean_dec(v___y_2729_);
    crate::leanh::lean_dec_ref(v___y_2728_);
    crate::leanh::lean_dec(v___y_2727_);
    crate::leanh::lean_dec_ref(v___y_2726_);
    return v_res_2731_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetDefEq___lam__0(
    mut v_mvarId_2732_: *mut crate::leanh::LeanObject,
    mut v___x_2733_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2734_: *mut crate::leanh::LeanObject,
    mut v___y_2735_: *mut crate::leanh::LeanObject,
    mut v___y_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2745_: u8 = 0;
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2761_: u8 = 0;
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut v_unused_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_a_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_a_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_unused_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v_a_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_a_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2732_);
                v___x_2740_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2732_,
                    v___x_2733_,
                    v___y_2735_,
                    v___y_2736_,
                    v___y_2737_,
                    v___y_2738_,
                );
                if crate::leanh::lean_obj_tag(v___x_2740_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2740_, 1);
                    crate::leanh::lean_inc(v_mvarId_2732_);
                    v___x_2741_ = l_Lean_MVarId_getType(
                        v_mvarId_2732_,
                        v___y_2735_,
                        v___y_2736_,
                        v___y_2737_,
                        v___y_2738_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2741_) == 0 {
                        v_a_2742_ = crate::leanh::lean_ctor_get(v___x_2741_, 0);
                        v_isSharedCheck_2812_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2741_)) as u8;
                        if v_isSharedCheck_2812_ == 0 {
                            v___x_2744_ = v___x_2741_;
                            v_isShared_2745_ = v_isSharedCheck_2812_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2742_);
                            crate::leanh::lean_dec(v___x_2741_);
                            v___x_2744_ = crate::leanh::lean_box(0);
                            v_isShared_2745_ = v_isSharedCheck_2812_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_targetNew_2734_);
                        crate::leanh::lean_dec(v_mvarId_2732_);
                        v_a_2813_ = crate::leanh::lean_ctor_get(v___x_2741_, 0);
                        v_isSharedCheck_2820_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2741_)) as u8;
                        if v_isSharedCheck_2820_ == 0 {
                            v___x_2815_ = v___x_2741_;
                            v_isShared_2816_ = v_isSharedCheck_2820_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2813_);
                            crate::leanh::lean_dec(v___x_2741_);
                            v___x_2815_ = crate::leanh::lean_box(0);
                            v_isShared_2816_ = v_isSharedCheck_2820_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_targetNew_2734_);
                    crate::leanh::lean_dec(v_mvarId_2732_);
                    v_a_2821_ = crate::leanh::lean_ctor_get(v___x_2740_, 0);
                    v_isSharedCheck_2828_ = (!crate::leanh::lean_is_exclusive(v___x_2740_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2823_ = v___x_2740_;
                        v_isShared_2824_ = v_isSharedCheck_2828_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2821_);
                        crate::leanh::lean_dec(v___x_2740_);
                        v___x_2823_ = crate::leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2828_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2746_ = lean_expr_equal(v_a_2742_, v_targetNew_2734_);
                if v___x_2746_ == 0 {
                    crate::leanh::lean_del_object(v___x_2744_);
                    v___x_2747_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_2742_, v___y_2736_);
                    v_a_2748_ = crate::leanh::lean_ctor_get(v___x_2747_, 0);
                    crate::leanh::lean_inc(v_a_2748_);
                    crate::leanh::lean_dec_ref(v___x_2747_);
                    v___x_2749_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_targetNew_2734_, v___y_2736_);
                    v_a_2750_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                    crate::leanh::lean_inc(v_a_2750_);
                    crate::leanh::lean_dec_ref(v___x_2749_);
                    v___x_2751_ = lean_expr_equal(v_a_2748_, v_a_2750_);
                    if v___x_2751_ == 0 {
                        crate::leanh::lean_inc(v_mvarId_2732_);
                        v___x_2752_ = l_Lean_MVarId_getTag(
                            v_mvarId_2732_,
                            v___y_2735_,
                            v___y_2736_,
                            v___y_2737_,
                            v___y_2738_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2752_) == 0 {
                            v_a_2753_ = crate::leanh::lean_ctor_get(v___x_2752_, 0);
                            crate::leanh::lean_inc(v_a_2753_);
                            crate::leanh::lean_dec_ref_known(v___x_2752_, 1);
                            v___x_2754_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v_a_2750_,
                                v_a_2753_,
                                v___y_2735_,
                                v___y_2736_,
                                v___y_2737_,
                                v___y_2738_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2754_) == 0 {
                                v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2754_, 0);
                                crate::leanh::lean_inc_n(v_a_2755_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2754_, 1);
                                v___x_2756_ = l_Lean_Meta_mkExpectedTypeHint(
                                    v_a_2755_,
                                    v_a_2748_,
                                    v___y_2735_,
                                    v___y_2736_,
                                    v___y_2737_,
                                    v___y_2738_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2756_) == 0 {
                                    v_a_2757_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                                    crate::leanh::lean_inc(v_a_2757_);
                                    crate::leanh::lean_dec_ref_known(v___x_2756_, 1);
                                    v___x_2758_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_2732_, v_a_2757_, v___y_2736_);
                                    v_isSharedCheck_2766_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2758_)) as u8;
                                    if v_isSharedCheck_2766_ == 0 {
                                        v_unused_2767_ =
                                            crate::leanh::lean_ctor_get(v___x_2758_, 0);
                                        crate::leanh::lean_dec(v_unused_2767_);
                                        v___x_2760_ = v___x_2758_;
                                        v_isShared_2761_ = v_isSharedCheck_2766_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2758_);
                                        v___x_2760_ = crate::leanh::lean_box(0);
                                        v_isShared_2761_ = v_isSharedCheck_2766_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2755_);
                                    crate::leanh::lean_dec(v_mvarId_2732_);
                                    v_a_2768_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                                    v_isSharedCheck_2775_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2756_)) as u8;
                                    if v_isSharedCheck_2775_ == 0 {
                                        v___x_2770_ = v___x_2756_;
                                        v_isShared_2771_ = v_isSharedCheck_2775_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2768_);
                                        crate::leanh::lean_dec(v___x_2756_);
                                        v___x_2770_ = crate::leanh::lean_box(0);
                                        v_isShared_2771_ = v_isSharedCheck_2775_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2748_);
                                crate::leanh::lean_dec(v_mvarId_2732_);
                                v_a_2776_ = crate::leanh::lean_ctor_get(v___x_2754_, 0);
                                v_isSharedCheck_2783_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2754_)) as u8;
                                if v_isSharedCheck_2783_ == 0 {
                                    v___x_2778_ = v___x_2754_;
                                    v_isShared_2779_ = v_isSharedCheck_2783_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2776_);
                                    crate::leanh::lean_dec(v___x_2754_);
                                    v___x_2778_ = crate::leanh::lean_box(0);
                                    v_isShared_2779_ = v_isSharedCheck_2783_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2750_);
                            crate::leanh::lean_dec(v_a_2748_);
                            crate::leanh::lean_dec(v_mvarId_2732_);
                            v_a_2784_ = crate::leanh::lean_ctor_get(v___x_2752_, 0);
                            v_isSharedCheck_2791_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2752_)) as u8;
                            if v_isSharedCheck_2791_ == 0 {
                                v___x_2786_ = v___x_2752_;
                                v_isShared_2787_ = v_isSharedCheck_2791_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2784_);
                                crate::leanh::lean_dec(v___x_2752_);
                                v___x_2786_ = crate::leanh::lean_box(0);
                                v_isShared_2787_ = v_isSharedCheck_2791_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2750_);
                        crate::leanh::lean_inc(v_mvarId_2732_);
                        v___x_2792_ =
                            l_Lean_MVarId_setType___redArg(v_mvarId_2732_, v_a_2748_, v___y_2736_);
                        if crate::leanh::lean_obj_tag(v___x_2792_) == 0 {
                            v_isSharedCheck_2799_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2792_)) as u8;
                            if v_isSharedCheck_2799_ == 0 {
                                v_unused_2800_ = crate::leanh::lean_ctor_get(v___x_2792_, 0);
                                crate::leanh::lean_dec(v_unused_2800_);
                                v___x_2794_ = v___x_2792_;
                                v_isShared_2795_ = v_isSharedCheck_2799_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2792_);
                                v___x_2794_ = crate::leanh::lean_box(0);
                                v_isShared_2795_ = v_isSharedCheck_2799_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_2732_);
                            v_a_2801_ = crate::leanh::lean_ctor_get(v___x_2792_, 0);
                            v_isSharedCheck_2808_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2792_)) as u8;
                            if v_isSharedCheck_2808_ == 0 {
                                v___x_2803_ = v___x_2792_;
                                v_isShared_2804_ = v_isSharedCheck_2808_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2801_);
                                crate::leanh::lean_dec(v___x_2792_);
                                v___x_2803_ = crate::leanh::lean_box(0);
                                v_isShared_2804_ = v_isSharedCheck_2808_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2742_);
                    crate::leanh::lean_dec_ref(v_targetNew_2734_);
                    if v_isShared_2745_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2744_, 0, v_mvarId_2732_);
                        v___x_2810_ = v___x_2744_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2811_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_mvarId_2732_);
                        v___x_2810_ = v_reuseFailAlloc_2811_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2762_ = l_Lean_Expr_mvarId_x21(v_a_2755_);
                crate::leanh::lean_dec(v_a_2755_);
                if v_isShared_2761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2760_, 0, v___x_2762_);
                    v___x_2764_ = v___x_2760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
                    v___x_2764_ = v_reuseFailAlloc_2765_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2764_;
            }
            4 => {
                if v_isShared_2771_ == 0 {
                    v___x_2773_ = v___x_2770_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
                    v___x_2773_ = v_reuseFailAlloc_2774_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2773_;
            }
            6 => {
                if v_isShared_2779_ == 0 {
                    v___x_2781_ = v___x_2778_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2781_;
            }
            8 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2789_;
            }
            10 => {
                if v_isShared_2795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2794_, 0, v_mvarId_2732_);
                    v___x_2797_ = v___x_2794_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_mvarId_2732_);
                    v___x_2797_ = v_reuseFailAlloc_2798_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2797_;
            }
            12 => {
                if v_isShared_2804_ == 0 {
                    v___x_2806_ = v___x_2803_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
                    v___x_2806_ = v_reuseFailAlloc_2807_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2806_;
            }
            14 => {
                return v___x_2810_;
            }
            15 => {
                if v_isShared_2816_ == 0 {
                    v___x_2818_ = v___x_2815_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
                    v___x_2818_ = v_reuseFailAlloc_2819_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2818_;
            }
            17 => {
                if v_isShared_2824_ == 0 {
                    v___x_2826_ = v___x_2823_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
                    v___x_2826_ = v_reuseFailAlloc_2827_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed(
    mut v_mvarId_2829_: *mut crate::leanh::LeanObject,
    mut v___x_2830_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Lean_MVarId_replaceTargetDefEq___lam__0(
        v_mvarId_2829_,
        v___x_2830_,
        v_targetNew_2831_,
        v___y_2832_,
        v___y_2833_,
        v___y_2834_,
        v___y_2835_,
    );
    crate::leanh::lean_dec(v___y_2835_);
    crate::leanh::lean_dec_ref(v___y_2834_);
    crate::leanh::lean_dec(v___y_2833_);
    crate::leanh::lean_dec_ref(v___y_2832_);
    return v_res_2837_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetDefEq(
    mut v_mvarId_2841_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = l_Lean_MVarId_replaceTargetDefEq___closed__1;
    crate::leanh::lean_inc(v_mvarId_2841_);
    v___f_2849_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_replaceTargetDefEq___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2849_, 0, v_mvarId_2841_);
    crate::leanh::lean_closure_set(v___f_2849_, 1, v___x_2848_);
    crate::leanh::lean_closure_set(v___f_2849_, 2, v_targetNew_2842_);
    v___x_2850_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_2841_,
        v___f_2849_,
        v_a_2843_,
        v_a_2844_,
        v_a_2845_,
        v_a_2846_,
    );
    return v___x_2850_;
}
pub unsafe fn l_Lean_MVarId_replaceTargetDefEq___boxed(
    mut v_mvarId_2851_: *mut crate::leanh::LeanObject,
    mut v_targetNew_2852_: *mut crate::leanh::LeanObject,
    mut v_a_2853_: *mut crate::leanh::LeanObject,
    mut v_a_2854_: *mut crate::leanh::LeanObject,
    mut v_a_2855_: *mut crate::leanh::LeanObject,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
    mut v_a_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Lean_MVarId_replaceTargetDefEq(
        v_mvarId_2851_,
        v_targetNew_2852_,
        v_a_2853_,
        v_a_2854_,
        v_a_2855_,
        v_a_2856_,
    );
    crate::leanh::lean_dec(v_a_2856_);
    crate::leanh::lean_dec_ref(v_a_2855_);
    crate::leanh::lean_dec(v_a_2854_);
    crate::leanh::lean_dec_ref(v_a_2853_);
    return v_res_2858_;
}
pub unsafe fn l_Lean_MVarId_replace___lam__0(
    mut v_mvarId_2859_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2860_: *mut crate::leanh::LeanObject,
    mut v_val_2861_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_2862_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2879_: u8 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_a_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2895_: u8 = 0;
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2899_: u8 = 0;
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_a_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v_val_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut v_val_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_type_x3f_2863_) == 0 {
                    crate::leanh::lean_inc(v___y_2867_);
                    crate::leanh::lean_inc_ref(v___y_2866_);
                    crate::leanh::lean_inc(v___y_2865_);
                    crate::leanh::lean_inc_ref(v___y_2864_);
                    crate::leanh::lean_inc_ref(v_val_2861_);
                    v___x_2915_ = lean_infer_type(
                        v_val_2861_,
                        v___y_2864_,
                        v___y_2865_,
                        v___y_2866_,
                        v___y_2867_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2915_) == 0 {
                        v_a_2916_ = crate::leanh::lean_ctor_get(v___x_2915_, 0);
                        crate::leanh::lean_inc(v_a_2916_);
                        crate::leanh::lean_dec_ref_known(v___x_2915_, 1);
                        v_a_2902_ = v_a_2916_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2867_);
                        crate::leanh::lean_dec_ref(v___y_2866_);
                        crate::leanh::lean_dec(v___y_2865_);
                        crate::leanh::lean_dec_ref(v___y_2864_);
                        crate::leanh::lean_dec(v_userName_x3f_2862_);
                        crate::leanh::lean_dec_ref(v_val_2861_);
                        crate::leanh::lean_dec(v_fvarId_2860_);
                        crate::leanh::lean_dec(v_mvarId_2859_);
                        v_a_2917_ = crate::leanh::lean_ctor_get(v___x_2915_, 0);
                        v_isSharedCheck_2924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2915_)) as u8;
                        if v_isSharedCheck_2924_ == 0 {
                            v___x_2919_ = v___x_2915_;
                            v_isShared_2920_ = v_isSharedCheck_2924_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2917_);
                            crate::leanh::lean_dec(v___x_2915_);
                            v___x_2919_ = crate::leanh::lean_box(0);
                            v_isShared_2920_ = v_isSharedCheck_2924_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_val_2925_ = crate::leanh::lean_ctor_get(v_type_x3f_2863_, 0);
                    crate::leanh::lean_inc(v_val_2925_);
                    crate::leanh::lean_dec_ref_known(v_type_x3f_2863_, 1);
                    v_a_2902_ = v_val_2925_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fvarId_2860_);
                v___x_2872_ = l_Lean_MVarId_assertAfter_x27(
                    v_mvarId_2859_,
                    v_fvarId_2860_,
                    v_a_2871_,
                    v___y_2870_,
                    v_val_2861_,
                    v___y_2864_,
                    v___y_2865_,
                    v___y_2866_,
                    v___y_2867_,
                );
                if crate::leanh::lean_obj_tag(v___x_2872_) == 0 {
                    v_a_2873_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                    crate::leanh::lean_inc(v_a_2873_);
                    crate::leanh::lean_dec_ref_known(v___x_2872_, 1);
                    v_fvarId_2874_ = crate::leanh::lean_ctor_get(v_a_2873_, 0);
                    v_mvarId_2875_ = crate::leanh::lean_ctor_get(v_a_2873_, 1);
                    v_subst_2876_ = crate::leanh::lean_ctor_get(v_a_2873_, 2);
                    v_isSharedCheck_2900_ = (!crate::leanh::lean_is_exclusive(v_a_2873_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2878_ = v_a_2873_;
                        v_isShared_2879_ = v_isSharedCheck_2900_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_subst_2876_);
                        crate::leanh::lean_inc(v_mvarId_2875_);
                        crate::leanh::lean_inc(v_fvarId_2874_);
                        crate::leanh::lean_dec(v_a_2873_);
                        v___x_2878_ = crate::leanh::lean_box(0);
                        v_isShared_2879_ = v_isSharedCheck_2900_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2867_);
                    crate::leanh::lean_dec_ref(v___y_2866_);
                    crate::leanh::lean_dec(v___y_2865_);
                    crate::leanh::lean_dec_ref(v___y_2864_);
                    crate::leanh::lean_dec(v_fvarId_2860_);
                    return v___x_2872_;
                }
            }
            2 => {
                v___x_2880_ = l_Lean_MVarId_tryClear(
                    v_mvarId_2875_,
                    v_fvarId_2860_,
                    v___y_2864_,
                    v___y_2865_,
                    v___y_2866_,
                    v___y_2867_,
                );
                crate::leanh::lean_dec(v___y_2867_);
                crate::leanh::lean_dec_ref(v___y_2866_);
                crate::leanh::lean_dec(v___y_2865_);
                crate::leanh::lean_dec_ref(v___y_2864_);
                if crate::leanh::lean_obj_tag(v___x_2880_) == 0 {
                    v_a_2881_ = crate::leanh::lean_ctor_get(v___x_2880_, 0);
                    v_isSharedCheck_2891_ = (!crate::leanh::lean_is_exclusive(v___x_2880_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v___x_2883_ = v___x_2880_;
                        v_isShared_2884_ = v_isSharedCheck_2891_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2881_);
                        crate::leanh::lean_dec(v___x_2880_);
                        v___x_2883_ = crate::leanh::lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2891_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2878_);
                    crate::leanh::lean_dec(v_subst_2876_);
                    crate::leanh::lean_dec(v_fvarId_2874_);
                    v_a_2892_ = crate::leanh::lean_ctor_get(v___x_2880_, 0);
                    v_isSharedCheck_2899_ = (!crate::leanh::lean_is_exclusive(v___x_2880_)) as u8;
                    if v_isSharedCheck_2899_ == 0 {
                        v___x_2894_ = v___x_2880_;
                        v_isShared_2895_ = v_isSharedCheck_2899_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2892_);
                        crate::leanh::lean_dec(v___x_2880_);
                        v___x_2894_ = crate::leanh::lean_box(0);
                        v_isShared_2895_ = v_isSharedCheck_2899_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2878_, 1, v_a_2881_);
                    v___x_2886_ = v___x_2878_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fvarId_2874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_a_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_subst_2876_);
                    v___x_2886_ = v_reuseFailAlloc_2890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2883_, 0, v___x_2886_);
                    v___x_2888_ = v___x_2883_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2888_;
            }
            6 => {
                if v_isShared_2895_ == 0 {
                    v___x_2897_ = v___x_2894_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2898_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
                    v___x_2897_ = v_reuseFailAlloc_2898_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2897_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_userName_x3f_2862_) == 0 {
                    crate::leanh::lean_inc(v_fvarId_2860_);
                    v___x_2903_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_2860_,
                        v___y_2864_,
                        v___y_2866_,
                        v___y_2867_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2903_) == 0 {
                        v_a_2904_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                        crate::leanh::lean_inc(v_a_2904_);
                        crate::leanh::lean_dec_ref_known(v___x_2903_, 1);
                        v___x_2905_ = l_Lean_LocalDecl_userName(v_a_2904_);
                        crate::leanh::lean_dec(v_a_2904_);
                        v___y_2870_ = v_a_2902_;
                        v_a_2871_ = v___x_2905_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2902_);
                        crate::leanh::lean_dec(v___y_2867_);
                        crate::leanh::lean_dec_ref(v___y_2866_);
                        crate::leanh::lean_dec(v___y_2865_);
                        crate::leanh::lean_dec_ref(v___y_2864_);
                        crate::leanh::lean_dec_ref(v_val_2861_);
                        crate::leanh::lean_dec(v_fvarId_2860_);
                        crate::leanh::lean_dec(v_mvarId_2859_);
                        v_a_2906_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                        v_isSharedCheck_2913_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2903_)) as u8;
                        if v_isSharedCheck_2913_ == 0 {
                            v___x_2908_ = v___x_2903_;
                            v_isShared_2909_ = v_isSharedCheck_2913_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2906_);
                            crate::leanh::lean_dec(v___x_2903_);
                            v___x_2908_ = crate::leanh::lean_box(0);
                            v_isShared_2909_ = v_isSharedCheck_2913_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v_val_2914_ = crate::leanh::lean_ctor_get(v_userName_x3f_2862_, 0);
                    crate::leanh::lean_inc(v_val_2914_);
                    crate::leanh::lean_dec_ref_known(v_userName_x3f_2862_, 1);
                    v___y_2870_ = v_a_2902_;
                    v_a_2871_ = v_val_2914_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                if v_isShared_2909_ == 0 {
                    v___x_2911_ = v___x_2908_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2911_;
            }
            11 => {
                if v_isShared_2920_ == 0 {
                    v___x_2922_ = v___x_2919_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2922_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replace___lam__0___boxed(
    mut v_mvarId_2926_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2927_: *mut crate::leanh::LeanObject,
    mut v_val_2928_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_2929_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_MVarId_replace___lam__0(
        v_mvarId_2926_,
        v_fvarId_2927_,
        v_val_2928_,
        v_userName_x3f_2929_,
        v_type_x3f_2930_,
        v___y_2931_,
        v___y_2932_,
        v___y_2933_,
        v___y_2934_,
    );
    return v_res_2936_;
}
pub unsafe fn l_Lean_MVarId_replace(
    mut v_mvarId_2937_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2938_: *mut crate::leanh::LeanObject,
    mut v_val_2939_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_2940_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_2941_: *mut crate::leanh::LeanObject,
    mut v_a_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_2937_);
    v___f_2947_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_replace___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2947_, 0, v_mvarId_2937_);
    crate::leanh::lean_closure_set(v___f_2947_, 1, v_fvarId_2938_);
    crate::leanh::lean_closure_set(v___f_2947_, 2, v_val_2939_);
    crate::leanh::lean_closure_set(v___f_2947_, 3, v_userName_x3f_2941_);
    crate::leanh::lean_closure_set(v___f_2947_, 4, v_type_x3f_2940_);
    v___x_2948_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_2937_,
        v___f_2947_,
        v_a_2942_,
        v_a_2943_,
        v_a_2944_,
        v_a_2945_,
    );
    return v___x_2948_;
}
pub unsafe fn l_Lean_MVarId_replace___boxed(
    mut v_mvarId_2949_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2950_: *mut crate::leanh::LeanObject,
    mut v_val_2951_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_2952_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
    mut v_a_2958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2959_ = l_Lean_MVarId_replace(
        v_mvarId_2949_,
        v_fvarId_2950_,
        v_val_2951_,
        v_type_x3f_2952_,
        v_userName_x3f_2953_,
        v_a_2954_,
        v_a_2955_,
        v_a_2956_,
        v_a_2957_,
    );
    crate::leanh::lean_dec(v_a_2957_);
    crate::leanh::lean_dec_ref(v_a_2956_);
    crate::leanh::lean_dec(v_a_2955_);
    crate::leanh::lean_dec_ref(v_a_2954_);
    return v_res_2959_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDecl___lam__0(
    mut v_eqProof_2960_: *mut crate::leanh::LeanObject,
    mut v___x_2961_: *mut crate::leanh::LeanObject,
    mut v_typeNew_2962_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2963_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2970_ = l_Lean_Meta_mkEqMP(
                    v_eqProof_2960_,
                    v___x_2961_,
                    v___y_2965_,
                    v___y_2966_,
                    v___y_2967_,
                    v___y_2968_,
                );
                if crate::leanh::lean_obj_tag(v___x_2970_) == 0 {
                    v_a_2971_ = crate::leanh::lean_ctor_get(v___x_2970_, 0);
                    crate::leanh::lean_inc(v_a_2971_);
                    crate::leanh::lean_dec_ref_known(v___x_2970_, 1);
                    v___x_2972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2972_, 0, v_typeNew_2962_);
                    v___x_2973_ = crate::leanh::lean_box(0);
                    v___x_2974_ = l_Lean_MVarId_replace(
                        v_mvarId_2963_,
                        v_fvarId_2964_,
                        v_a_2971_,
                        v___x_2972_,
                        v___x_2973_,
                        v___y_2965_,
                        v___y_2966_,
                        v___y_2967_,
                        v___y_2968_,
                    );
                    return v___x_2974_;
                } else {
                    crate::leanh::lean_dec(v_fvarId_2964_);
                    crate::leanh::lean_dec(v_mvarId_2963_);
                    crate::leanh::lean_dec_ref(v_typeNew_2962_);
                    v_a_2975_ = crate::leanh::lean_ctor_get(v___x_2970_, 0);
                    v_isSharedCheck_2982_ = (!crate::leanh::lean_is_exclusive(v___x_2970_)) as u8;
                    if v_isSharedCheck_2982_ == 0 {
                        v___x_2977_ = v___x_2970_;
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2975_);
                        crate::leanh::lean_dec(v___x_2970_);
                        v___x_2977_ = crate::leanh::lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2978_ == 0 {
                    v___x_2980_ = v___x_2977_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceLocalDecl___lam__0___boxed(
    mut v_eqProof_2983_: *mut crate::leanh::LeanObject,
    mut v___x_2984_: *mut crate::leanh::LeanObject,
    mut v_typeNew_2985_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2986_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_MVarId_replaceLocalDecl___lam__0(
        v_eqProof_2983_,
        v___x_2984_,
        v_typeNew_2985_,
        v_mvarId_2986_,
        v_fvarId_2987_,
        v___y_2988_,
        v___y_2989_,
        v___y_2990_,
        v___y_2991_,
    );
    crate::leanh::lean_dec(v___y_2991_);
    crate::leanh::lean_dec_ref(v___y_2990_);
    crate::leanh::lean_dec(v___y_2989_);
    crate::leanh::lean_dec_ref(v___y_2988_);
    return v_res_2993_;
}
pub unsafe fn _init_l_Lean_MVarId_replaceLocalDecl___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2994_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2994_;
}
pub unsafe fn _init_l_Lean_MVarId_replaceLocalDecl___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_replaceLocalDecl___closed__0),
        core::ptr::addr_of_mut!(l_Lean_MVarId_replaceLocalDecl___closed__0_once),
        _init_l_Lean_MVarId_replaceLocalDecl___closed__0,
    );
    v___x_2996_ = l_StateRefT_x27_instMonad___redArg(v___x_2995_);
    return v___x_2996_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDecl(
    mut v_mvarId_3001_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3002_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3003_: *mut crate::leanh::LeanObject,
    mut v_eqProof_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_a_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v_toFunctor_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___f_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17__overap_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_unused_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut v_unused_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3010_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_replaceLocalDecl___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_replaceLocalDecl___closed__1_once),
                    _init_l_Lean_MVarId_replaceLocalDecl___closed__1,
                );
                v_toApplicative_3011_ = crate::leanh::lean_ctor_get(v___x_3010_, 0);
                v_toFunctor_3012_ = crate::leanh::lean_ctor_get(v_toApplicative_3011_, 0);
                v_toSeq_3013_ = crate::leanh::lean_ctor_get(v_toApplicative_3011_, 2);
                v_toSeqLeft_3014_ = crate::leanh::lean_ctor_get(v_toApplicative_3011_, 3);
                v_toSeqRight_3015_ = crate::leanh::lean_ctor_get(v_toApplicative_3011_, 4);
                v___f_3016_ = l_Lean_MVarId_replaceLocalDecl___closed__2;
                v___f_3017_ = l_Lean_MVarId_replaceLocalDecl___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_3012_, 2);
                v___f_3018_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3018_, 0, v_toFunctor_3012_);
                v___f_3019_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3019_, 0, v_toFunctor_3012_);
                v___x_3020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3020_, 0, v___f_3018_);
                crate::leanh::lean_ctor_set(v___x_3020_, 1, v___f_3019_);
                crate::leanh::lean_inc(v_toSeqRight_3015_);
                v___f_3021_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3021_, 0, v_toSeqRight_3015_);
                crate::leanh::lean_inc(v_toSeqLeft_3014_);
                v___f_3022_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3022_, 0, v_toSeqLeft_3014_);
                crate::leanh::lean_inc(v_toSeq_3013_);
                v___f_3023_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3023_, 0, v_toSeq_3013_);
                v___x_3024_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3020_);
                crate::leanh::lean_ctor_set(v___x_3024_, 1, v___f_3016_);
                crate::leanh::lean_ctor_set(v___x_3024_, 2, v___f_3023_);
                crate::leanh::lean_ctor_set(v___x_3024_, 3, v___f_3022_);
                crate::leanh::lean_ctor_set(v___x_3024_, 4, v___f_3021_);
                v___x_3025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_3024_);
                crate::leanh::lean_ctor_set(v___x_3025_, 1, v___f_3017_);
                v___x_3026_ = l_StateRefT_x27_instMonad___redArg(v___x_3025_);
                v___x_3027_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_3027_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3027_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3027_, 2, v___x_3026_);
                v___x_3028_ = l_instMonadControlTOfPure___redArg(v___x_3027_);
                v_toApplicative_3029_ = crate::leanh::lean_ctor_get(v___x_3010_, 0);
                v_toFunctor_3030_ = crate::leanh::lean_ctor_get(v_toApplicative_3029_, 0);
                v_toSeq_3031_ = crate::leanh::lean_ctor_get(v_toApplicative_3029_, 2);
                v_toSeqLeft_3032_ = crate::leanh::lean_ctor_get(v_toApplicative_3029_, 3);
                v_toSeqRight_3033_ = crate::leanh::lean_ctor_get(v_toApplicative_3029_, 4);
                crate::leanh::lean_inc_ref_n(v_toFunctor_3030_, 2);
                v___f_3034_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3034_, 0, v_toFunctor_3030_);
                v___f_3035_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3035_, 0, v_toFunctor_3030_);
                v___x_3036_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3036_, 0, v___f_3034_);
                crate::leanh::lean_ctor_set(v___x_3036_, 1, v___f_3035_);
                crate::leanh::lean_inc(v_toSeqRight_3033_);
                v___f_3037_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3037_, 0, v_toSeqRight_3033_);
                crate::leanh::lean_inc(v_toSeqLeft_3032_);
                v___f_3038_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3038_, 0, v_toSeqLeft_3032_);
                crate::leanh::lean_inc(v_toSeq_3031_);
                v___f_3039_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3039_, 0, v_toSeq_3031_);
                v___x_3040_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3040_, 0, v___x_3036_);
                crate::leanh::lean_ctor_set(v___x_3040_, 1, v___f_3016_);
                crate::leanh::lean_ctor_set(v___x_3040_, 2, v___f_3039_);
                crate::leanh::lean_ctor_set(v___x_3040_, 3, v___f_3038_);
                crate::leanh::lean_ctor_set(v___x_3040_, 4, v___f_3037_);
                v___x_3041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3041_, 0, v___x_3040_);
                crate::leanh::lean_ctor_set(v___x_3041_, 1, v___f_3017_);
                v___x_3042_ = l_StateRefT_x27_instMonad___redArg(v___x_3041_);
                v_toApplicative_3043_ = crate::leanh::lean_ctor_get(v___x_3042_, 0);
                v_isSharedCheck_3074_ = (!crate::leanh::lean_is_exclusive(v___x_3042_)) as u8;
                if v_isSharedCheck_3074_ == 0 {
                    v_unused_3075_ = crate::leanh::lean_ctor_get(v___x_3042_, 1);
                    crate::leanh::lean_dec(v_unused_3075_);
                    v___x_3045_ = v___x_3042_;
                    v_isShared_3046_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3043_);
                    crate::leanh::lean_dec(v___x_3042_);
                    v___x_3045_ = crate::leanh::lean_box(0);
                    v_isShared_3046_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3047_ = crate::leanh::lean_ctor_get(v_toApplicative_3043_, 0);
                v_toSeq_3048_ = crate::leanh::lean_ctor_get(v_toApplicative_3043_, 2);
                v_toSeqLeft_3049_ = crate::leanh::lean_ctor_get(v_toApplicative_3043_, 3);
                v_toSeqRight_3050_ = crate::leanh::lean_ctor_get(v_toApplicative_3043_, 4);
                v_isSharedCheck_3072_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3043_)) as u8;
                if v_isSharedCheck_3072_ == 0 {
                    v_unused_3073_ = crate::leanh::lean_ctor_get(v_toApplicative_3043_, 1);
                    crate::leanh::lean_dec(v_unused_3073_);
                    v___x_3052_ = v_toApplicative_3043_;
                    v_isShared_3053_ = v_isSharedCheck_3072_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3050_);
                    crate::leanh::lean_inc(v_toSeqLeft_3049_);
                    crate::leanh::lean_inc(v_toSeq_3048_);
                    crate::leanh::lean_inc(v_toFunctor_3047_);
                    crate::leanh::lean_dec(v_toApplicative_3043_);
                    v___x_3052_ = crate::leanh::lean_box(0);
                    v_isShared_3053_ = v_isSharedCheck_3072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3054_ = l_Lean_MVarId_replaceLocalDecl___closed__4;
                v___f_3055_ = l_Lean_MVarId_replaceLocalDecl___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_3047_);
                v___f_3056_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3056_, 0, v_toFunctor_3047_);
                v___f_3057_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3057_, 0, v_toFunctor_3047_);
                v___x_3058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v___f_3056_);
                crate::leanh::lean_ctor_set(v___x_3058_, 1, v___f_3057_);
                v___f_3059_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3059_, 0, v_toSeqRight_3050_);
                v___f_3060_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3060_, 0, v_toSeqLeft_3049_);
                v___f_3061_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3061_, 0, v_toSeq_3048_);
                if v_isShared_3053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3052_, 4, v___f_3059_);
                    crate::leanh::lean_ctor_set(v___x_3052_, 3, v___f_3060_);
                    crate::leanh::lean_ctor_set(v___x_3052_, 2, v___f_3061_);
                    crate::leanh::lean_ctor_set(v___x_3052_, 1, v___f_3054_);
                    crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3058_);
                    v___x_3063_ = v___x_3052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___f_3054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 2, v___f_3061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 3, v___f_3060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 4, v___f_3059_);
                    v___x_3063_ = v_reuseFailAlloc_3071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3046_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3045_, 1, v___f_3055_);
                    crate::leanh::lean_ctor_set(v___x_3045_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3045_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___f_3055_);
                    v___x_3065_ = v_reuseFailAlloc_3070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_fvarId_3002_);
                v___x_3066_ = l_Lean_mkFVar(v_fvarId_3002_);
                crate::leanh::lean_inc(v_mvarId_3001_);
                v___f_3067_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MVarId_replaceLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_3067_, 0, v_eqProof_3004_);
                crate::leanh::lean_closure_set(v___f_3067_, 1, v___x_3066_);
                crate::leanh::lean_closure_set(v___f_3067_, 2, v_typeNew_3003_);
                crate::leanh::lean_closure_set(v___f_3067_, 3, v_mvarId_3001_);
                crate::leanh::lean_closure_set(v___f_3067_, 4, v_fvarId_3002_);
                v___x_17__overap_3068_ = l_Lean_MVarId_withContext___redArg(
                    v___x_3028_,
                    v___x_3065_,
                    v_mvarId_3001_,
                    v___f_3067_,
                );
                crate::leanh::lean_inc(v_a_3008_);
                crate::leanh::lean_inc_ref(v_a_3007_);
                crate::leanh::lean_inc(v_a_3006_);
                crate::leanh::lean_inc_ref(v_a_3005_);
                v___x_3069_ = crate::leanh::lean_apply_5(
                    v___x_17__overap_3068_,
                    v_a_3005_,
                    v_a_3006_,
                    v_a_3007_,
                    v_a_3008_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceLocalDecl___boxed(
    mut v_mvarId_3076_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3077_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3078_: *mut crate::leanh::LeanObject,
    mut v_eqProof_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ = l_Lean_MVarId_replaceLocalDecl(
        v_mvarId_3076_,
        v_fvarId_3077_,
        v_typeNew_3078_,
        v_eqProof_3079_,
        v_a_3080_,
        v_a_3081_,
        v_a_3082_,
        v_a_3083_,
    );
    crate::leanh::lean_dec(v_a_3083_);
    crate::leanh::lean_dec_ref(v_a_3082_);
    crate::leanh::lean_dec(v_a_3081_);
    crate::leanh::lean_dec_ref(v_a_3080_);
    return v_res_3085_;
}
pub unsafe fn l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(
    mut v_decls_3086_: *mut crate::leanh::LeanObject,
    mut v_x_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3093_ = l_Lean_Meta_withLocalInstancesImp___redArg(
                    v_decls_3086_,
                    v_x_3087_,
                    v___y_3088_,
                    v___y_3089_,
                    v___y_3090_,
                    v___y_3091_,
                );
                if crate::leanh::lean_obj_tag(v___x_3093_) == 0 {
                    v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                    v_isSharedCheck_3101_ = (!crate::leanh::lean_is_exclusive(v___x_3093_)) as u8;
                    if v_isSharedCheck_3101_ == 0 {
                        v___x_3096_ = v___x_3093_;
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3094_);
                        crate::leanh::lean_dec(v___x_3093_);
                        v___x_3096_ = crate::leanh::lean_box(0);
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                    v_isSharedCheck_3109_ = (!crate::leanh::lean_is_exclusive(v___x_3093_)) as u8;
                    if v_isSharedCheck_3109_ == 0 {
                        v___x_3104_ = v___x_3093_;
                        v_isShared_3105_ = v_isSharedCheck_3109_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3102_);
                        crate::leanh::lean_dec(v___x_3093_);
                        v___x_3104_ = crate::leanh::lean_box(0);
                        v_isShared_3105_ = v_isSharedCheck_3109_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3099_;
            }
            3 => {
                if v_isShared_3105_ == 0 {
                    v___x_3107_ = v___x_3104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg___boxed(
    mut v_decls_3110_: *mut crate::leanh::LeanObject,
    mut v_x_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
    mut v___y_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ =
        l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(
            v_decls_3110_,
            v_x_3111_,
            v___y_3112_,
            v___y_3113_,
            v___y_3114_,
            v___y_3115_,
        );
    crate::leanh::lean_dec(v___y_3115_);
    crate::leanh::lean_dec_ref(v___y_3114_);
    crate::leanh::lean_dec(v___y_3113_);
    crate::leanh::lean_dec_ref(v___y_3112_);
    crate::leanh::lean_dec(v_decls_3110_);
    return v_res_3117_;
}
pub unsafe fn l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(
    mut v_00_u03b1_3118_: *mut crate::leanh::LeanObject,
    mut v_decls_3119_: *mut crate::leanh::LeanObject,
    mut v_x_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ =
        l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___redArg(
            v_decls_3119_,
            v_x_3120_,
            v___y_3121_,
            v___y_3122_,
            v___y_3123_,
            v___y_3124_,
        );
    return v___x_3126_;
}
pub unsafe fn l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed(
    mut v_00_u03b1_3127_: *mut crate::leanh::LeanObject,
    mut v_decls_3128_: *mut crate::leanh::LeanObject,
    mut v_x_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
    mut v___y_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0(
        v_00_u03b1_3127_,
        v_decls_3128_,
        v_x_3129_,
        v___y_3130_,
        v___y_3131_,
        v___y_3132_,
        v___y_3133_,
    );
    crate::leanh::lean_dec(v___y_3133_);
    crate::leanh::lean_dec_ref(v___y_3132_);
    crate::leanh::lean_dec(v___y_3131_);
    crate::leanh::lean_dec_ref(v___y_3130_);
    crate::leanh::lean_dec(v_decls_3128_);
    return v_res_3135_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(
    mut v_lctx_3136_: *mut crate::leanh::LeanObject,
    mut v_x_3137_: *mut crate::leanh::LeanObject,
    mut v___y_3138_: *mut crate::leanh::LeanObject,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyedConfig_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_3144_: u8 = 0;
    let mut v_zetaDeltaSet_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3150_: u8 = 0;
    let mut v_inTypeClassResolution_3151_: u8 = 0;
    let mut v_cacheInferType_3152_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_3143_ = crate::leanh::lean_ctor_get(v___y_3138_, 0);
    v_trackZetaDelta_3144_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3138_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_3145_ = crate::leanh::lean_ctor_get(v___y_3138_, 1);
    v_localInstances_3146_ = crate::leanh::lean_ctor_get(v___y_3138_, 3);
    v_defEqCtx_x3f_3147_ = crate::leanh::lean_ctor_get(v___y_3138_, 4);
    v_synthPendingDepth_3148_ = crate::leanh::lean_ctor_get(v___y_3138_, 5);
    v_canUnfold_x3f_3149_ = crate::leanh::lean_ctor_get(v___y_3138_, 6);
    v_univApprox_3150_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3138_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_3151_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3138_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_3152_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3138_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
    );
    crate::leanh::lean_inc(v_canUnfold_x3f_3149_);
    crate::leanh::lean_inc(v_synthPendingDepth_3148_);
    crate::leanh::lean_inc(v_defEqCtx_x3f_3147_);
    crate::leanh::lean_inc_ref(v_localInstances_3146_);
    crate::leanh::lean_inc(v_zetaDeltaSet_3145_);
    crate::leanh::lean_inc_ref(v_keyedConfig_3143_);
    v___x_3153_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_3153_, 0, v_keyedConfig_3143_);
    crate::leanh::lean_ctor_set(v___x_3153_, 1, v_zetaDeltaSet_3145_);
    crate::leanh::lean_ctor_set(v___x_3153_, 2, v_lctx_3136_);
    crate::leanh::lean_ctor_set(v___x_3153_, 3, v_localInstances_3146_);
    crate::leanh::lean_ctor_set(v___x_3153_, 4, v_defEqCtx_x3f_3147_);
    crate::leanh::lean_ctor_set(v___x_3153_, 5, v_synthPendingDepth_3148_);
    crate::leanh::lean_ctor_set(v___x_3153_, 6, v_canUnfold_x3f_3149_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3153_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_3144_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3153_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_3150_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3153_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_3151_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3153_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_3152_,
    );
    crate::leanh::lean_inc(v___y_3141_);
    crate::leanh::lean_inc_ref(v___y_3140_);
    crate::leanh::lean_inc(v___y_3139_);
    v___x_3154_ = crate::leanh::lean_apply_5(
        v_x_3137_,
        v___x_3153_,
        v___y_3139_,
        v___y_3140_,
        v___y_3141_,
        crate::leanh::lean_box(0),
    );
    return v___x_3154_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg___boxed(
    mut v_lctx_3155_: *mut crate::leanh::LeanObject,
    mut v_x_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
    mut v___y_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ =
        l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(
            v_lctx_3155_,
            v_x_3156_,
            v___y_3157_,
            v___y_3158_,
            v___y_3159_,
            v___y_3160_,
        );
    crate::leanh::lean_dec(v___y_3160_);
    crate::leanh::lean_dec_ref(v___y_3159_);
    crate::leanh::lean_dec(v___y_3158_);
    crate::leanh::lean_dec_ref(v___y_3157_);
    return v_res_3162_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(
    mut v_00_u03b1_3163_: *mut crate::leanh::LeanObject,
    mut v_lctx_3164_: *mut crate::leanh::LeanObject,
    mut v_x_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3171_ =
        l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(
            v_lctx_3164_,
            v_x_3165_,
            v___y_3166_,
            v___y_3167_,
            v___y_3168_,
            v___y_3169_,
        );
    return v___x_3171_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___boxed(
    mut v_00_u03b1_3172_: *mut crate::leanh::LeanObject,
    mut v_lctx_3173_: *mut crate::leanh::LeanObject,
    mut v_x_3174_: *mut crate::leanh::LeanObject,
    mut v___y_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3180_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1(
        v_00_u03b1_3172_,
        v_lctx_3173_,
        v_x_3174_,
        v___y_3175_,
        v___y_3176_,
        v___y_3177_,
        v___y_3178_,
    );
    crate::leanh::lean_dec(v___y_3178_);
    crate::leanh::lean_dec_ref(v___y_3177_);
    crate::leanh::lean_dec(v___y_3176_);
    crate::leanh::lean_dec_ref(v___y_3175_);
    return v_res_3180_;
}
pub unsafe fn l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(
    mut v_mvarId_3181_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3182_: *mut crate::leanh::LeanObject,
    mut v_type_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3186_ = lean_st_ref_take(v___y_3184_);
                v_mctx_3187_ = crate::leanh::lean_ctor_get(v___x_3186_, 0);
                v_cache_3188_ = crate::leanh::lean_ctor_get(v___x_3186_, 1);
                v_zetaDeltaFVarIds_3189_ = crate::leanh::lean_ctor_get(v___x_3186_, 2);
                v_postponed_3190_ = crate::leanh::lean_ctor_get(v___x_3186_, 3);
                v_diag_3191_ = crate::leanh::lean_ctor_get(v___x_3186_, 4);
                v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v___x_3186_)) as u8;
                if v_isSharedCheck_3202_ == 0 {
                    v___x_3193_ = v___x_3186_;
                    v_isShared_3194_ = v_isSharedCheck_3202_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3191_);
                    crate::leanh::lean_inc(v_postponed_3190_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3189_);
                    crate::leanh::lean_inc(v_cache_3188_);
                    crate::leanh::lean_inc(v_mctx_3187_);
                    crate::leanh::lean_dec(v___x_3186_);
                    v___x_3193_ = crate::leanh::lean_box(0);
                    v_isShared_3194_ = v_isSharedCheck_3202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3195_ = l_Lean_MetavarContext_setFVarType(
                    v_mctx_3187_,
                    v_mvarId_3181_,
                    v_fvarId_3182_,
                    v_type_3183_,
                );
                if v_isShared_3194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3195_);
                    v___x_3197_ = v___x_3193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_cache_3188_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3201_,
                        2,
                        v_zetaDeltaFVarIds_3189_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_postponed_3190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_diag_3191_);
                    v___x_3197_ = v_reuseFailAlloc_3201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3198_ = lean_st_ref_set(v___y_3184_, v___x_3197_);
                v___x_3199_ = crate::leanh::lean_box(0);
                v___x_3200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3200_, 0, v___x_3199_);
                return v___x_3200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg___boxed(
    mut v_mvarId_3203_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3204_: *mut crate::leanh::LeanObject,
    mut v_type_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3208_ =
        l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(
            v_mvarId_3203_,
            v_fvarId_3204_,
            v_type_3205_,
            v___y_3206_,
        );
    crate::leanh::lean_dec(v___y_3206_);
    return v_res_3208_;
}
pub unsafe fn l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(
    mut v_mvarId_3209_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3210_: *mut crate::leanh::LeanObject,
    mut v_type_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ =
        l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(
            v_mvarId_3209_,
            v_fvarId_3210_,
            v_type_3211_,
            v___y_3213_,
        );
    return v___x_3217_;
}
pub unsafe fn l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___boxed(
    mut v_mvarId_3218_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3219_: *mut crate::leanh::LeanObject,
    mut v_type_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3226_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2(
        v_mvarId_3218_,
        v_fvarId_3219_,
        v_type_3220_,
        v___y_3221_,
        v___y_3222_,
        v___y_3223_,
        v___y_3224_,
    );
    crate::leanh::lean_dec(v___y_3224_);
    crate::leanh::lean_dec_ref(v___y_3223_);
    crate::leanh::lean_dec(v___y_3222_);
    crate::leanh::lean_dec_ref(v___y_3221_);
    return v_res_3226_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(
    mut v_mvarId_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3237_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_unused_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut v_a_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3262_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3227_);
                v___x_3233_ = l_Lean_MVarId_getDecl(
                    v_mvarId_3227_,
                    v___y_3228_,
                    v___y_3229_,
                    v___y_3230_,
                    v___y_3231_,
                );
                if crate::leanh::lean_obj_tag(v___x_3233_) == 0 {
                    v_a_3234_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                    crate::leanh::lean_inc(v_a_3234_);
                    crate::leanh::lean_dec_ref_known(v___x_3233_, 1);
                    v_userName_3235_ = crate::leanh::lean_ctor_get(v_a_3234_, 0);
                    crate::leanh::lean_inc(v_userName_3235_);
                    v_type_3236_ = crate::leanh::lean_ctor_get(v_a_3234_, 2);
                    crate::leanh::lean_inc_ref(v_type_3236_);
                    v_kind_3237_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3234_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    crate::leanh::lean_dec(v_a_3234_);
                    v___x_3238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3238_, 0, v_type_3236_);
                    v___x_3239_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_3238_,
                        v_kind_3237_,
                        v_userName_3235_,
                        v___y_3228_,
                        v___y_3229_,
                        v___y_3230_,
                        v___y_3231_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3239_) == 0 {
                        v_a_3240_ = crate::leanh::lean_ctor_get(v___x_3239_, 0);
                        crate::leanh::lean_inc_n(v_a_3240_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3239_, 1);
                        v___x_3241_ = l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(v_mvarId_3227_, v_a_3240_, v___y_3229_);
                        v_isSharedCheck_3249_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3241_)) as u8;
                        if v_isSharedCheck_3249_ == 0 {
                            v_unused_3250_ = crate::leanh::lean_ctor_get(v___x_3241_, 0);
                            crate::leanh::lean_dec(v_unused_3250_);
                            v___x_3243_ = v___x_3241_;
                            v_isShared_3244_ = v_isSharedCheck_3249_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3241_);
                            v___x_3243_ = crate::leanh::lean_box(0);
                            v_isShared_3244_ = v_isSharedCheck_3249_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_3227_);
                        v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3239_, 0);
                        v_isSharedCheck_3258_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3239_)) as u8;
                        if v_isSharedCheck_3258_ == 0 {
                            v___x_3253_ = v___x_3239_;
                            v_isShared_3254_ = v_isSharedCheck_3258_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3251_);
                            crate::leanh::lean_dec(v___x_3239_);
                            v___x_3253_ = crate::leanh::lean_box(0);
                            v_isShared_3254_ = v_isSharedCheck_3258_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_3227_);
                    v_a_3259_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                    v_isSharedCheck_3266_ = (!crate::leanh::lean_is_exclusive(v___x_3233_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3261_ = v___x_3233_;
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3259_);
                        crate::leanh::lean_dec(v___x_3233_);
                        v___x_3261_ = crate::leanh::lean_box(0);
                        v_isShared_3262_ = v_isSharedCheck_3266_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3245_ = l_Lean_Expr_mvarId_x21(v_a_3240_);
                crate::leanh::lean_dec(v_a_3240_);
                if v_isShared_3244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3243_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3247_;
            }
            3 => {
                if v_isShared_3254_ == 0 {
                    v___x_3256_ = v___x_3253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3257_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
                    v___x_3256_ = v_reuseFailAlloc_3257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3256_;
            }
            5 => {
                if v_isShared_3262_ == 0 {
                    v___x_3264_ = v___x_3261_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3265_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
                    v___x_3264_ = v_reuseFailAlloc_3265_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed(
    mut v_mvarId_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3273_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__0(
        v_mvarId_3267_,
        v___y_3268_,
        v___y_3269_,
        v___y_3270_,
        v___y_3271_,
    );
    crate::leanh::lean_dec(v___y_3271_);
    crate::leanh::lean_dec_ref(v___y_3270_);
    crate::leanh::lean_dec(v___y_3269_);
    crate::leanh::lean_dec_ref(v___y_3268_);
    return v_res_3273_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(
    mut v_fvarId_3274_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3275_: *mut crate::leanh::LeanObject,
    mut v___f_3276_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v_lctx_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_unused_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_3274_);
                v___x_3283_ = l_Lean_FVarId_getType___redArg(
                    v_fvarId_3274_,
                    v___y_3278_,
                    v___y_3280_,
                    v___y_3281_,
                );
                if crate::leanh::lean_obj_tag(v___x_3283_) == 0 {
                    v_a_3284_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                    v_isSharedCheck_3313_ = (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v___x_3286_ = v___x_3283_;
                        v_isShared_3287_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3284_);
                        crate::leanh::lean_dec(v___x_3283_);
                        v___x_3286_ = crate::leanh::lean_box(0);
                        v_isShared_3287_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3278_);
                    crate::leanh::lean_dec(v_mvarId_3277_);
                    crate::leanh::lean_dec_ref(v___f_3276_);
                    crate::leanh::lean_dec_ref(v_typeNew_3275_);
                    crate::leanh::lean_dec(v_fvarId_3274_);
                    v_a_3314_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
                    v_isSharedCheck_3321_ = (!crate::leanh::lean_is_exclusive(v___x_3283_)) as u8;
                    if v_isSharedCheck_3321_ == 0 {
                        v___x_3316_ = v___x_3283_;
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3314_);
                        crate::leanh::lean_dec(v___x_3283_);
                        v___x_3316_ = crate::leanh::lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3288_ = lean_expr_equal(v_a_3284_, v_typeNew_3275_);
                if v___x_3288_ == 0 {
                    crate::leanh::lean_del_object(v___x_3286_);
                    v___x_3289_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_a_3284_, v___y_3279_);
                    v_a_3290_ = crate::leanh::lean_ctor_get(v___x_3289_, 0);
                    crate::leanh::lean_inc(v_a_3290_);
                    crate::leanh::lean_dec_ref(v___x_3289_);
                    v___x_3291_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v_typeNew_3275_, v___y_3279_);
                    v_a_3292_ = crate::leanh::lean_ctor_get(v___x_3291_, 0);
                    crate::leanh::lean_inc(v_a_3292_);
                    crate::leanh::lean_dec_ref(v___x_3291_);
                    v___x_3293_ = lean_expr_equal(v_a_3290_, v_a_3292_);
                    if v___x_3293_ == 0 {
                        crate::leanh::lean_dec(v_a_3290_);
                        crate::leanh::lean_dec(v_mvarId_3277_);
                        v_lctx_3294_ = crate::leanh::lean_ctor_get(v___y_3278_, 2);
                        crate::leanh::lean_inc(v_fvarId_3274_);
                        crate::leanh::lean_inc_ref(v_lctx_3294_);
                        v___x_3295_ =
                            l_Lean_LocalContext_setType(v_lctx_3294_, v_fvarId_3274_, v_a_3292_);
                        crate::leanh::lean_inc_ref(v___x_3295_);
                        v___x_3296_ = l_Lean_LocalContext_get_x21(v___x_3295_, v_fvarId_3274_);
                        v___x_3297_ = crate::leanh::lean_box(0);
                        v___x_3298_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3298_, 0, v___x_3296_);
                        crate::leanh::lean_ctor_set(v___x_3298_, 1, v___x_3297_);
                        v___x_3299_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalInstances___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__0___boxed as *mut core::ffi::c_void, 8, 3);
                        crate::leanh::lean_closure_set(v___x_3299_, 0, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_3299_, 1, v___x_3298_);
                        crate::leanh::lean_closure_set(v___x_3299_, 2, v___f_3276_);
                        v___x_3300_ = l_Lean_Meta_withLCtx_x27___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__1___redArg(v___x_3295_, v___x_3299_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
                        crate::leanh::lean_dec_ref(v___y_3278_);
                        return v___x_3300_;
                    } else {
                        crate::leanh::lean_dec(v_a_3292_);
                        crate::leanh::lean_dec_ref(v___y_3278_);
                        crate::leanh::lean_dec_ref(v___f_3276_);
                        crate::leanh::lean_inc(v_mvarId_3277_);
                        v___x_3301_ = l_Lean_MVarId_setFVarType___at___00Lean_MVarId_replaceLocalDeclDefEq_spec__2___redArg(v_mvarId_3277_, v_fvarId_3274_, v_a_3290_, v___y_3279_);
                        v_isSharedCheck_3308_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3301_)) as u8;
                        if v_isSharedCheck_3308_ == 0 {
                            v_unused_3309_ = crate::leanh::lean_ctor_get(v___x_3301_, 0);
                            crate::leanh::lean_dec(v_unused_3309_);
                            v___x_3303_ = v___x_3301_;
                            v_isShared_3304_ = v_isSharedCheck_3308_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3301_);
                            v___x_3303_ = crate::leanh::lean_box(0);
                            v_isShared_3304_ = v_isSharedCheck_3308_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3284_);
                    crate::leanh::lean_dec_ref(v___y_3278_);
                    crate::leanh::lean_dec_ref(v___f_3276_);
                    crate::leanh::lean_dec_ref(v_typeNew_3275_);
                    crate::leanh::lean_dec(v_fvarId_3274_);
                    if v_isShared_3287_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3286_, 0, v_mvarId_3277_);
                        v___x_3311_ = v___x_3286_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_mvarId_3277_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3303_, 0, v_mvarId_3277_);
                    v___x_3306_ = v___x_3303_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_mvarId_3277_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3306_;
            }
            4 => {
                return v___x_3311_;
            }
            5 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed(
    mut v_fvarId_3322_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3323_: *mut crate::leanh::LeanObject,
    mut v___f_3324_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_MVarId_replaceLocalDeclDefEq___lam__1(
        v_fvarId_3322_,
        v_typeNew_3323_,
        v___f_3324_,
        v_mvarId_3325_,
        v___y_3326_,
        v___y_3327_,
        v___y_3328_,
        v___y_3329_,
    );
    crate::leanh::lean_dec(v___y_3329_);
    crate::leanh::lean_dec_ref(v___y_3328_);
    crate::leanh::lean_dec(v___y_3327_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq(
    mut v_mvarId_3332_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3333_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_mvarId_3332_, 2);
    v___f_3340_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_replaceLocalDeclDefEq___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3340_, 0, v_mvarId_3332_);
    v___f_3341_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_replaceLocalDeclDefEq___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3341_, 0, v_fvarId_3333_);
    crate::leanh::lean_closure_set(v___f_3341_, 1, v_typeNew_3334_);
    crate::leanh::lean_closure_set(v___f_3341_, 2, v___f_3340_);
    crate::leanh::lean_closure_set(v___f_3341_, 3, v_mvarId_3332_);
    v___x_3342_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_3332_,
        v___f_3341_,
        v_a_3335_,
        v_a_3336_,
        v_a_3337_,
        v_a_3338_,
    );
    return v___x_3342_;
}
pub unsafe fn l_Lean_MVarId_replaceLocalDeclDefEq___boxed(
    mut v_mvarId_3343_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3344_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3351_ = l_Lean_MVarId_replaceLocalDeclDefEq(
        v_mvarId_3343_,
        v_fvarId_3344_,
        v_typeNew_3345_,
        v_a_3346_,
        v_a_3347_,
        v_a_3348_,
        v_a_3349_,
    );
    crate::leanh::lean_dec(v_a_3349_);
    crate::leanh::lean_dec_ref(v_a_3348_);
    crate::leanh::lean_dec(v_a_3347_);
    crate::leanh::lean_dec_ref(v_a_3346_);
    return v_res_3351_;
}
pub unsafe fn _init_l_Lean_MVarId_change___lam__0___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = l_Lean_MVarId_change___lam__0___closed__0;
    v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
    return v___x_3354_;
}
pub unsafe fn _init_l_Lean_MVarId_change___lam__0___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3356_ = l_Lean_MVarId_change___lam__0___closed__2;
    v___x_3357_ = l_Lean_stringToMessageData(v___x_3356_);
    return v___x_3357_;
}
pub unsafe fn l_Lean_MVarId_change___lam__0(
    mut v_mvarId_3358_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_3359_: u8,
    mut v_targetNew_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3386_: u8 = 0;
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_a_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3358_);
                v___x_3366_ = l_Lean_MVarId_getType(
                    v_mvarId_3358_,
                    v___y_3361_,
                    v___y_3362_,
                    v___y_3363_,
                    v___y_3364_,
                );
                if crate::leanh::lean_obj_tag(v___x_3366_) == 0 {
                    if v_checkDefEq_3359_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3366_, 1);
                        v___x_3367_ = l_Lean_MVarId_replaceTargetDefEq(
                            v_mvarId_3358_,
                            v_targetNew_3360_,
                            v___y_3361_,
                            v___y_3362_,
                            v___y_3363_,
                            v___y_3364_,
                        );
                        return v___x_3367_;
                    } else {
                        v_a_3368_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                        crate::leanh::lean_inc_n(v_a_3368_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3366_, 1);
                        crate::leanh::lean_inc_ref(v_targetNew_3360_);
                        v___x_3369_ = l_Lean_Meta_isExprDefEq(
                            v_a_3368_,
                            v_targetNew_3360_,
                            v___y_3361_,
                            v___y_3362_,
                            v___y_3363_,
                            v___y_3364_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3369_) == 0 {
                            v_a_3370_ = crate::leanh::lean_ctor_get(v___x_3369_, 0);
                            crate::leanh::lean_inc(v_a_3370_);
                            crate::leanh::lean_dec_ref_known(v___x_3369_, 1);
                            v___x_3371_ = (crate::leanh::lean_unbox(v_a_3370_) as u8);
                            crate::leanh::lean_dec(v_a_3370_);
                            if v___x_3371_ == 0 {
                                v___x_3372_ = l_Lean_MVarId_replaceTargetDefEq___closed__1;
                                v___x_3373_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_change___lam__0___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_change___lam__0___closed__1_once
                                    ),
                                    _init_l_Lean_MVarId_change___lam__0___closed__1,
                                );
                                crate::leanh::lean_inc_ref(v_targetNew_3360_);
                                v___x_3374_ = l_Lean_indentExpr(v_targetNew_3360_);
                                v___x_3375_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3373_);
                                crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3374_);
                                v___x_3376_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_change___lam__0___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_change___lam__0___closed__3_once
                                    ),
                                    _init_l_Lean_MVarId_change___lam__0___closed__3,
                                );
                                v___x_3377_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3375_);
                                crate::leanh::lean_ctor_set(v___x_3377_, 1, v___x_3376_);
                                v___x_3378_ = l_Lean_indentExpr(v_a_3368_);
                                v___x_3379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3379_, 0, v___x_3377_);
                                crate::leanh::lean_ctor_set(v___x_3379_, 1, v___x_3378_);
                                v___x_3380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3380_, 0, v___x_3379_);
                                crate::leanh::lean_inc(v_mvarId_3358_);
                                v___x_3381_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_3372_,
                                    v_mvarId_3358_,
                                    v___x_3380_,
                                    v___y_3361_,
                                    v___y_3362_,
                                    v___y_3363_,
                                    v___y_3364_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3381_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3381_, 1);
                                    v___x_3382_ = l_Lean_MVarId_replaceTargetDefEq(
                                        v_mvarId_3358_,
                                        v_targetNew_3360_,
                                        v___y_3361_,
                                        v___y_3362_,
                                        v___y_3363_,
                                        v___y_3364_,
                                    );
                                    return v___x_3382_;
                                } else {
                                    crate::leanh::lean_dec_ref(v_targetNew_3360_);
                                    crate::leanh::lean_dec(v_mvarId_3358_);
                                    v_a_3383_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                                    v_isSharedCheck_3390_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3381_)) as u8;
                                    if v_isSharedCheck_3390_ == 0 {
                                        v___x_3385_ = v___x_3381_;
                                        v_isShared_3386_ = v_isSharedCheck_3390_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3383_);
                                        crate::leanh::lean_dec(v___x_3381_);
                                        v___x_3385_ = crate::leanh::lean_box(0);
                                        v_isShared_3386_ = v_isSharedCheck_3390_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3368_);
                                v___x_3391_ = l_Lean_MVarId_replaceTargetDefEq(
                                    v_mvarId_3358_,
                                    v_targetNew_3360_,
                                    v___y_3361_,
                                    v___y_3362_,
                                    v___y_3363_,
                                    v___y_3364_,
                                );
                                return v___x_3391_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3368_);
                            crate::leanh::lean_dec_ref(v_targetNew_3360_);
                            crate::leanh::lean_dec(v_mvarId_3358_);
                            v_a_3392_ = crate::leanh::lean_ctor_get(v___x_3369_, 0);
                            v_isSharedCheck_3399_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3369_)) as u8;
                            if v_isSharedCheck_3399_ == 0 {
                                v___x_3394_ = v___x_3369_;
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3392_);
                                crate::leanh::lean_dec(v___x_3369_);
                                v___x_3394_ = crate::leanh::lean_box(0);
                                v_isShared_3395_ = v_isSharedCheck_3399_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_targetNew_3360_);
                    crate::leanh::lean_dec(v_mvarId_3358_);
                    v_a_3400_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                    v_isSharedCheck_3407_ = (!crate::leanh::lean_is_exclusive(v___x_3366_)) as u8;
                    if v_isSharedCheck_3407_ == 0 {
                        v___x_3402_ = v___x_3366_;
                        v_isShared_3403_ = v_isSharedCheck_3407_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3400_);
                        crate::leanh::lean_dec(v___x_3366_);
                        v___x_3402_ = crate::leanh::lean_box(0);
                        v_isShared_3403_ = v_isSharedCheck_3407_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3386_ == 0 {
                    v___x_3388_ = v___x_3385_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
                    v___x_3388_ = v_reuseFailAlloc_3389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3388_;
            }
            3 => {
                if v_isShared_3395_ == 0 {
                    v___x_3397_ = v___x_3394_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3397_;
            }
            5 => {
                if v_isShared_3403_ == 0 {
                    v___x_3405_ = v___x_3402_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3406_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_change___lam__0___boxed(
    mut v_mvarId_3408_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_3409_: *mut crate::leanh::LeanObject,
    mut v_targetNew_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkDefEq_boxed_3416_: u8 = 0;
    let mut v_res_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkDefEq_boxed_3416_ = (crate::leanh::lean_unbox(v_checkDefEq_3409_) as u8);
    v_res_3417_ = l_Lean_MVarId_change___lam__0(
        v_mvarId_3408_,
        v_checkDefEq_boxed_3416_,
        v_targetNew_3410_,
        v___y_3411_,
        v___y_3412_,
        v___y_3413_,
        v___y_3414_,
    );
    crate::leanh::lean_dec(v___y_3414_);
    crate::leanh::lean_dec_ref(v___y_3413_);
    crate::leanh::lean_dec(v___y_3412_);
    crate::leanh::lean_dec_ref(v___y_3411_);
    return v_res_3417_;
}
pub unsafe fn l_Lean_MVarId_change(
    mut v_mvarId_3418_: *mut crate::leanh::LeanObject,
    mut v_targetNew_3419_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_3420_: u8,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
    mut v_a_3423_: *mut crate::leanh::LeanObject,
    mut v_a_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3426_ = crate::leanh::lean_box((v_checkDefEq_3420_) as usize);
    crate::leanh::lean_inc(v_mvarId_3418_);
    v___f_3427_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_change___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3427_, 0, v_mvarId_3418_);
    crate::leanh::lean_closure_set(v___f_3427_, 1, v___x_3426_);
    crate::leanh::lean_closure_set(v___f_3427_, 2, v_targetNew_3419_);
    v___x_3428_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_3418_,
        v___f_3427_,
        v_a_3421_,
        v_a_3422_,
        v_a_3423_,
        v_a_3424_,
    );
    return v___x_3428_;
}
pub unsafe fn l_Lean_MVarId_change___boxed(
    mut v_mvarId_3429_: *mut crate::leanh::LeanObject,
    mut v_targetNew_3430_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
    mut v_a_3435_: *mut crate::leanh::LeanObject,
    mut v_a_3436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkDefEq_boxed_3437_: u8 = 0;
    let mut v_res_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkDefEq_boxed_3437_ = (crate::leanh::lean_unbox(v_checkDefEq_3431_) as u8);
    v_res_3438_ = l_Lean_MVarId_change(
        v_mvarId_3429_,
        v_targetNew_3430_,
        v_checkDefEq_boxed_3437_,
        v_a_3432_,
        v_a_3433_,
        v_a_3434_,
        v_a_3435_,
    );
    crate::leanh::lean_dec(v_a_3435_);
    crate::leanh::lean_dec_ref(v_a_3434_);
    crate::leanh::lean_dec(v_a_3433_);
    crate::leanh::lean_dec_ref(v_a_3432_);
    return v_res_3438_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(
    mut v_t_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3444_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v_enabled_3460_: u8 = 0;
    let mut v_assignment_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3442_ = lean_st_ref_get(v___y_3440_);
                v_infoState_3443_ = crate::leanh::lean_ctor_get(v___x_3442_, 7);
                crate::leanh::lean_inc_ref(v_infoState_3443_);
                crate::leanh::lean_dec(v___x_3442_);
                v_enabled_3444_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3443_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_3443_);
                if v_enabled_3444_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_3439_);
                    v___x_3445_ = crate::leanh::lean_box(0);
                    v___x_3446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3445_);
                    return v___x_3446_;
                } else {
                    v___x_3447_ = lean_st_ref_take(v___y_3440_);
                    v_infoState_3448_ = crate::leanh::lean_ctor_get(v___x_3447_, 7);
                    v_env_3449_ = crate::leanh::lean_ctor_get(v___x_3447_, 0);
                    v_nextMacroScope_3450_ = crate::leanh::lean_ctor_get(v___x_3447_, 1);
                    v_ngen_3451_ = crate::leanh::lean_ctor_get(v___x_3447_, 2);
                    v_auxDeclNGen_3452_ = crate::leanh::lean_ctor_get(v___x_3447_, 3);
                    v_traceState_3453_ = crate::leanh::lean_ctor_get(v___x_3447_, 4);
                    v_cache_3454_ = crate::leanh::lean_ctor_get(v___x_3447_, 5);
                    v_messages_3455_ = crate::leanh::lean_ctor_get(v___x_3447_, 6);
                    v_snapshotTasks_3456_ = crate::leanh::lean_ctor_get(v___x_3447_, 8);
                    v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v___x_3447_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3458_ = v___x_3447_;
                        v_isShared_3459_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_3456_);
                        crate::leanh::lean_inc(v_infoState_3448_);
                        crate::leanh::lean_inc(v_messages_3455_);
                        crate::leanh::lean_inc(v_cache_3454_);
                        crate::leanh::lean_inc(v_traceState_3453_);
                        crate::leanh::lean_inc(v_auxDeclNGen_3452_);
                        crate::leanh::lean_inc(v_ngen_3451_);
                        crate::leanh::lean_inc(v_nextMacroScope_3450_);
                        crate::leanh::lean_inc(v_env_3449_);
                        crate::leanh::lean_dec(v___x_3447_);
                        v___x_3458_ = crate::leanh::lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_3460_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3448_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3461_ = crate::leanh::lean_ctor_get(v_infoState_3448_, 0);
                v_lazyAssignment_3462_ = crate::leanh::lean_ctor_get(v_infoState_3448_, 1);
                v_trees_3463_ = crate::leanh::lean_ctor_get(v_infoState_3448_, 2);
                v_isSharedCheck_3477_ = (!crate::leanh::lean_is_exclusive(v_infoState_3448_)) as u8;
                if v_isSharedCheck_3477_ == 0 {
                    v___x_3465_ = v_infoState_3448_;
                    v_isShared_3466_ = v_isSharedCheck_3477_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_3463_);
                    crate::leanh::lean_inc(v_lazyAssignment_3462_);
                    crate::leanh::lean_inc(v_assignment_3461_);
                    crate::leanh::lean_dec(v_infoState_3448_);
                    v___x_3465_ = crate::leanh::lean_box(0);
                    v_isShared_3466_ = v_isSharedCheck_3477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3467_ = l_Lean_PersistentArray_push___redArg(v_trees_3463_, v_t_3439_);
                if v_isShared_3466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3465_, 2, v___x_3467_);
                    v___x_3469_ = v___x_3465_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_assignment_3461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_lazyAssignment_3462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 2, v___x_3467_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3476_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_3460_,
                    );
                    v___x_3469_ = v_reuseFailAlloc_3476_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3458_, 7, v___x_3469_);
                    v___x_3471_ = v___x_3458_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_env_3449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_nextMacroScope_3450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_ngen_3451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_auxDeclNGen_3452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_traceState_3453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 5, v_cache_3454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 6, v_messages_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 7, v___x_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 8, v_snapshotTasks_3456_);
                    v___x_3471_ = v_reuseFailAlloc_3475_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3472_ = lean_st_ref_set(v___y_3440_, v___x_3471_);
                v___x_3473_ = crate::leanh::lean_box(0);
                v___x_3474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3474_, 0, v___x_3473_);
                return v___x_3474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg___boxed(
    mut v_t_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_3479_, v___y_3480_);
    crate::leanh::lean_dec(v___y_3480_);
    return v_res_3482_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3484_ = lean_mk_empty_array_with_capacity(v___x_3483_);
    v___x_3485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3485_, 0, v___x_3484_);
    return v___x_3485_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: usize = 0;
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = 5usize;
    v___x_3487_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3488_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3489_ = lean_mk_empty_array_with_capacity(v___x_3488_);
    v___x_3490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0_once
        ),
        _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__0,
    );
    v___x_3491_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3491_, 0, v___x_3490_);
    crate::leanh::lean_ctor_set(v___x_3491_, 1, v___x_3489_);
    crate::leanh::lean_ctor_set(v___x_3491_, 2, v___x_3487_);
    crate::leanh::lean_ctor_set(v___x_3491_, 3, v___x_3487_);
    crate::leanh::lean_ctor_set_usize(v___x_3491_, 4, v___x_3486_);
    return v___x_3491_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(
    mut v_t_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3500_: u8 = 0;
    v___x_3498_ = lean_st_ref_get(v___y_3496_);
    v_infoState_3499_ = crate::leanh::lean_ctor_get(v___x_3498_, 7);
    crate::leanh::lean_inc_ref(v_infoState_3499_);
    crate::leanh::lean_dec(v___x_3498_);
    v_enabled_3500_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_3499_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_3499_);
    if v_enabled_3500_ == 0 {
        let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_3492_);
        v___x_3501_ = crate::leanh::lean_box(0);
        v___x_3502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3502_, 0, v___x_3501_);
        return v___x_3502_;
    } else {
        let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3503_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1_once
            ),
            _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___closed__1,
        );
        v___x_3504_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3504_, 0, v_t_3492_);
        crate::leanh::lean_ctor_set(v___x_3504_, 1, v___x_3503_);
        v___x_3505_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v___x_3504_, v___y_3496_);
        return v___x_3505_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0___boxed(
    mut v_t_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(
        v_t_3506_,
        v___y_3507_,
        v___y_3508_,
        v___y_3509_,
        v___y_3510_,
    );
    crate::leanh::lean_dec(v___y_3510_);
    crate::leanh::lean_dec_ref(v___y_3509_);
    crate::leanh::lean_dec(v___y_3508_);
    crate::leanh::lean_dec_ref(v___y_3507_);
    return v_res_3512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(
    mut v_as_3513_: *mut crate::leanh::LeanObject,
    mut v_sz_3514_: usize,
    mut v_i_3515_: usize,
    mut v_b_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: usize = 0;
    let mut v___x_3525_: usize = 0;
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v_a_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3569_: u8 = 0;
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_reuseFailAlloc_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_unused_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3527_ = lean_usize_dec_lt(v_i_3515_, v_sz_3514_);
                if v___x_3527_ == 0 {
                    v___x_3528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3528_, 0, v_b_3516_);
                    return v___x_3528_;
                } else {
                    v_array_3529_ = crate::leanh::lean_ctor_get(v_b_3516_, 0);
                    v_start_3530_ = crate::leanh::lean_ctor_get(v_b_3516_, 1);
                    v_stop_3531_ = crate::leanh::lean_ctor_get(v_b_3516_, 2);
                    v___x_3532_ = lean_nat_dec_lt(v_start_3530_, v_stop_3531_);
                    if v___x_3532_ == 0 {
                        v___x_3533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3533_, 0, v_b_3516_);
                        return v___x_3533_;
                    } else {
                        crate::leanh::lean_inc(v_stop_3531_);
                        crate::leanh::lean_inc(v_start_3530_);
                        crate::leanh::lean_inc_ref(v_array_3529_);
                        v_isSharedCheck_3572_ = (!crate::leanh::lean_is_exclusive(v_b_3516_)) as u8;
                        if v_isSharedCheck_3572_ == 0 {
                            v_unused_3573_ = crate::leanh::lean_ctor_get(v_b_3516_, 2);
                            crate::leanh::lean_dec(v_unused_3573_);
                            v_unused_3574_ = crate::leanh::lean_ctor_get(v_b_3516_, 1);
                            crate::leanh::lean_dec(v_unused_3574_);
                            v_unused_3575_ = crate::leanh::lean_ctor_get(v_b_3516_, 0);
                            crate::leanh::lean_dec(v_unused_3575_);
                            v___x_3535_ = v_b_3516_;
                            v_isShared_3536_ = v_isSharedCheck_3572_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_3516_);
                            v___x_3535_ = crate::leanh::lean_box(0);
                            v_isShared_3536_ = v_isSharedCheck_3572_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3524_ = 1usize;
                v___x_3525_ = lean_usize_add(v_i_3515_, v___x_3524_);
                v_i_3515_ = v___x_3525_;
                v_b_3516_ = v_a_3523_;
                state = 0;
                continue;
            }
            2 => {
                v_a_3537_ = lean_array_uget(v_as_3513_, v_i_3515_);
                v___x_3538_ = lean_array_fget(v_array_3529_, v_start_3530_);
                v___x_3539_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3540_ = lean_nat_add(v_start_3530_, v___x_3539_);
                crate::leanh::lean_dec(v_start_3530_);
                if v_isShared_3536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3535_, 1, v___x_3540_);
                    v___x_3542_ = v___x_3535_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_array_3529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_stop_3531_);
                    v___x_3542_ = v_reuseFailAlloc_3571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3537_) == 1 {
                    v_val_3543_ = crate::leanh::lean_ctor_get(v_a_3537_, 0);
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v_a_3537_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3545_ = v_a_3537_;
                        v_isShared_3546_ = v_isSharedCheck_3570_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3543_);
                        crate::leanh::lean_dec(v_a_3537_);
                        v___x_3545_ = crate::leanh::lean_box(0);
                        v_isShared_3546_ = v_isSharedCheck_3570_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3538_);
                    crate::leanh::lean_dec(v_a_3537_);
                    v_a_3523_ = v___x_3542_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v___x_3538_);
                v___x_3547_ = l_Lean_FVarId_getUserName___redArg(
                    v___x_3538_,
                    v___y_3517_,
                    v___y_3519_,
                    v___y_3520_,
                );
                if crate::leanh::lean_obj_tag(v___x_3547_) == 0 {
                    v_a_3548_ = crate::leanh::lean_ctor_get(v___x_3547_, 0);
                    crate::leanh::lean_inc(v_a_3548_);
                    crate::leanh::lean_dec_ref_known(v___x_3547_, 1);
                    v___x_3549_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3549_, 0, v_a_3548_);
                    crate::leanh::lean_ctor_set(v___x_3549_, 1, v___x_3538_);
                    crate::leanh::lean_ctor_set(v___x_3549_, 2, v_val_3543_);
                    if v_isShared_3546_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3545_, 11);
                        crate::leanh::lean_ctor_set(v___x_3545_, 0, v___x_3549_);
                        v___x_3551_ = v___x_3545_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(11, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3549_);
                        v___x_3551_ = v_reuseFailAlloc_3561_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3545_);
                    crate::leanh::lean_dec(v_val_3543_);
                    crate::leanh::lean_dec_ref(v___x_3542_);
                    crate::leanh::lean_dec(v___x_3538_);
                    v_a_3562_ = crate::leanh::lean_ctor_get(v___x_3547_, 0);
                    v_isSharedCheck_3569_ = (!crate::leanh::lean_is_exclusive(v___x_3547_)) as u8;
                    if v_isSharedCheck_3569_ == 0 {
                        v___x_3564_ = v___x_3547_;
                        v_isShared_3565_ = v_isSharedCheck_3569_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3562_);
                        crate::leanh::lean_dec(v___x_3547_);
                        v___x_3564_ = crate::leanh::lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3569_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3552_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0(
                    v___x_3551_,
                    v___y_3517_,
                    v___y_3518_,
                    v___y_3519_,
                    v___y_3520_,
                );
                if crate::leanh::lean_obj_tag(v___x_3552_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3552_, 1);
                    v_a_3523_ = v___x_3542_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_3542_);
                    v_a_3553_ = crate::leanh::lean_ctor_get(v___x_3552_, 0);
                    v_isSharedCheck_3560_ = (!crate::leanh::lean_is_exclusive(v___x_3552_)) as u8;
                    if v_isSharedCheck_3560_ == 0 {
                        v___x_3555_ = v___x_3552_;
                        v_isShared_3556_ = v_isSharedCheck_3560_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3553_);
                        crate::leanh::lean_dec(v___x_3552_);
                        v___x_3555_ = crate::leanh::lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3560_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3556_ == 0 {
                    v___x_3558_ = v___x_3555_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3558_;
            }
            8 => {
                if v_isShared_3565_ == 0 {
                    v___x_3567_ = v___x_3564_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3568_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
                    v___x_3567_ = v_reuseFailAlloc_3568_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1___boxed(
    mut v_as_3576_: *mut crate::leanh::LeanObject,
    mut v_sz_3577_: *mut crate::leanh::LeanObject,
    mut v_i_3578_: *mut crate::leanh::LeanObject,
    mut v_b_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3585_: usize = 0;
    let mut v_i_boxed_3586_: usize = 0;
    let mut v_res_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3585_ = crate::leanh::lean_unbox_usize(v_sz_3577_);
    crate::leanh::lean_dec(v_sz_3577_);
    v_i_boxed_3586_ = crate::leanh::lean_unbox_usize(v_i_3578_);
    crate::leanh::lean_dec(v_i_3578_);
    v_res_3587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_as_3576_, v_sz_boxed_3585_, v_i_boxed_3586_, v_b_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
    crate::leanh::lean_dec(v___y_3583_);
    crate::leanh::lean_dec_ref(v___y_3582_);
    crate::leanh::lean_dec(v___y_3581_);
    crate::leanh::lean_dec_ref(v___y_3580_);
    crate::leanh::lean_dec_ref(v_as_3576_);
    return v_res_3587_;
}
pub unsafe fn l_Lean_MVarId_withReverted___redArg___lam__0(
    mut v_fst_3588_: *mut crate::leanh::LeanObject,
    mut v_sz_3589_: usize,
    mut v___x_3590_: usize,
    mut v___x_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut v_unused_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_withReverted_spec__1(v_fst_3588_, v_sz_3589_, v___x_3590_, v___x_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
                if crate::leanh::lean_obj_tag(v___x_3597_) == 0 {
                    v_isSharedCheck_3605_ = (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v_unused_3606_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                        crate::leanh::lean_dec(v_unused_3606_);
                        v___x_3599_ = v___x_3597_;
                        v_isShared_3600_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3597_);
                        v___x_3599_ = crate::leanh::lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3607_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                    v_isSharedCheck_3614_ = (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                    if v_isSharedCheck_3614_ == 0 {
                        v___x_3609_ = v___x_3597_;
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3607_);
                        crate::leanh::lean_dec(v___x_3597_);
                        v___x_3609_ = crate::leanh::lean_box(0);
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3601_ = crate::leanh::lean_box(0);
                if v_isShared_3600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3601_);
                    v___x_3603_ = v___x_3599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3603_;
            }
            3 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withReverted___redArg___lam__0___boxed(
    mut v_fst_3615_: *mut crate::leanh::LeanObject,
    mut v_sz_3616_: *mut crate::leanh::LeanObject,
    mut v___x_3617_: *mut crate::leanh::LeanObject,
    mut v___x_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3624_: usize = 0;
    let mut v___x_3386__boxed_3625_: usize = 0;
    let mut v_res_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3624_ = crate::leanh::lean_unbox_usize(v_sz_3616_);
    crate::leanh::lean_dec(v_sz_3616_);
    v___x_3386__boxed_3625_ = crate::leanh::lean_unbox_usize(v___x_3617_);
    crate::leanh::lean_dec(v___x_3617_);
    v_res_3626_ = l_Lean_MVarId_withReverted___redArg___lam__0(
        v_fst_3615_,
        v_sz_boxed_3624_,
        v___x_3386__boxed_3625_,
        v___x_3618_,
        v___y_3619_,
        v___y_3620_,
        v___y_3621_,
        v___y_3622_,
    );
    crate::leanh::lean_dec(v___y_3622_);
    crate::leanh::lean_dec_ref(v___y_3621_);
    crate::leanh::lean_dec(v___y_3620_);
    crate::leanh::lean_dec_ref(v___y_3619_);
    crate::leanh::lean_dec_ref(v_fst_3615_);
    return v_res_3626_;
}
pub unsafe fn l_Lean_MVarId_withReverted___redArg(
    mut v_mvarId_3629_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3630_: *mut crate::leanh::LeanObject,
    mut v_k_3631_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_3632_: u8,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_3635_: *mut crate::leanh::LeanObject,
    mut v_a_3636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3638_: u8 = 0;
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3662_: usize = 0;
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v_unused_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3694_: u8 = 0;
    let mut v_a_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3698_: u8 = 0;
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut v_a_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3638_ = 1;
                v___x_3639_ = l_Lean_MVarId_revert(
                    v_mvarId_3629_,
                    v_fvarIds_3630_,
                    v___x_3638_,
                    v_clearAuxDeclsInsteadOfRevert_3632_,
                    v_a_3633_,
                    v_a_3634_,
                    v_a_3635_,
                    v_a_3636_,
                );
                if crate::leanh::lean_obj_tag(v___x_3639_) == 0 {
                    v_a_3640_ = crate::leanh::lean_ctor_get(v___x_3639_, 0);
                    crate::leanh::lean_inc(v_a_3640_);
                    crate::leanh::lean_dec_ref_known(v___x_3639_, 1);
                    v_fst_3641_ = crate::leanh::lean_ctor_get(v_a_3640_, 0);
                    crate::leanh::lean_inc(v_fst_3641_);
                    v_snd_3642_ = crate::leanh::lean_ctor_get(v_a_3640_, 1);
                    crate::leanh::lean_inc(v_snd_3642_);
                    crate::leanh::lean_dec(v_a_3640_);
                    crate::leanh::lean_inc(v_a_3636_);
                    crate::leanh::lean_inc_ref(v_a_3635_);
                    crate::leanh::lean_inc(v_a_3634_);
                    crate::leanh::lean_inc_ref(v_a_3633_);
                    v___x_3643_ = crate::leanh::lean_apply_7(
                        v_k_3631_,
                        v_snd_3642_,
                        v_fst_3641_,
                        v_a_3633_,
                        v_a_3634_,
                        v_a_3635_,
                        v_a_3636_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3643_) == 0 {
                        v_a_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                        crate::leanh::lean_inc(v_a_3644_);
                        crate::leanh::lean_dec_ref_known(v___x_3643_, 1);
                        v_snd_3645_ = crate::leanh::lean_ctor_get(v_a_3644_, 1);
                        crate::leanh::lean_inc(v_snd_3645_);
                        v_fst_3646_ = crate::leanh::lean_ctor_get(v_a_3644_, 0);
                        crate::leanh::lean_inc(v_fst_3646_);
                        crate::leanh::lean_dec(v_a_3644_);
                        v_fst_3647_ = crate::leanh::lean_ctor_get(v_snd_3645_, 0);
                        crate::leanh::lean_inc(v_fst_3647_);
                        v_snd_3648_ = crate::leanh::lean_ctor_get(v_snd_3645_, 1);
                        crate::leanh::lean_inc(v_snd_3648_);
                        crate::leanh::lean_dec(v_snd_3645_);
                        v___x_3649_ = lean_array_get_size(v_fst_3647_);
                        v___x_3650_ = crate::leanh::lean_box(0);
                        v___x_3651_ = 0;
                        v___x_3652_ = l_Lean_Meta_introNCore(
                            v_snd_3648_,
                            v___x_3649_,
                            v___x_3650_,
                            v___x_3651_,
                            v___x_3638_,
                            v_a_3633_,
                            v_a_3634_,
                            v_a_3635_,
                            v_a_3636_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3652_) == 0 {
                            v_a_3653_ = crate::leanh::lean_ctor_get(v___x_3652_, 0);
                            crate::leanh::lean_inc(v_a_3653_);
                            crate::leanh::lean_dec_ref_known(v___x_3652_, 1);
                            v_fst_3654_ = crate::leanh::lean_ctor_get(v_a_3653_, 0);
                            v_snd_3655_ = crate::leanh::lean_ctor_get(v_a_3653_, 1);
                            v_isSharedCheck_3686_ =
                                (!crate::leanh::lean_is_exclusive(v_a_3653_)) as u8;
                            if v_isSharedCheck_3686_ == 0 {
                                v___x_3657_ = v_a_3653_;
                                v_isShared_3658_ = v_isSharedCheck_3686_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_3655_);
                                crate::leanh::lean_inc(v_fst_3654_);
                                crate::leanh::lean_dec(v_a_3653_);
                                v___x_3657_ = crate::leanh::lean_box(0);
                                v_isShared_3658_ = v_isSharedCheck_3686_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_3647_);
                            crate::leanh::lean_dec(v_fst_3646_);
                            v_a_3687_ = crate::leanh::lean_ctor_get(v___x_3652_, 0);
                            v_isSharedCheck_3694_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3652_)) as u8;
                            if v_isSharedCheck_3694_ == 0 {
                                v___x_3689_ = v___x_3652_;
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3687_);
                                crate::leanh::lean_dec(v___x_3652_);
                                v___x_3689_ = crate::leanh::lean_box(0);
                                v_isShared_3690_ = v_isSharedCheck_3694_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v_a_3695_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                        v_isSharedCheck_3702_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                        if v_isSharedCheck_3702_ == 0 {
                            v___x_3697_ = v___x_3643_;
                            v_isShared_3698_ = v_isSharedCheck_3702_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3695_);
                            crate::leanh::lean_dec(v___x_3643_);
                            v___x_3697_ = crate::leanh::lean_box(0);
                            v_isShared_3698_ = v_isSharedCheck_3702_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3631_);
                    v_a_3703_ = crate::leanh::lean_ctor_get(v___x_3639_, 0);
                    v_isSharedCheck_3710_ = (!crate::leanh::lean_is_exclusive(v___x_3639_)) as u8;
                    if v_isSharedCheck_3710_ == 0 {
                        v___x_3705_ = v___x_3639_;
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3703_);
                        crate::leanh::lean_dec(v___x_3639_);
                        v___x_3705_ = crate::leanh::lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3710_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3659_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3660_ = lean_array_get_size(v_fst_3654_);
                v___x_3661_ = l_Array_toSubarray___redArg(v_fst_3654_, v___x_3659_, v___x_3660_);
                v_sz_3662_ = lean_array_size(v_fst_3647_);
                v___x_3663_ = crate::leanh::lean_box_usize(v_sz_3662_);
                v___x_3664_ = l_Lean_MVarId_withReverted___redArg___boxed__const__1;
                v___f_3665_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MVarId_withReverted___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3665_, 0, v_fst_3647_);
                crate::leanh::lean_closure_set(v___f_3665_, 1, v___x_3663_);
                crate::leanh::lean_closure_set(v___f_3665_, 2, v___x_3664_);
                crate::leanh::lean_closure_set(v___f_3665_, 3, v___x_3661_);
                crate::leanh::lean_inc(v_snd_3655_);
                v___x_3666_ =
                    l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
                        v_snd_3655_,
                        v___f_3665_,
                        v_a_3633_,
                        v_a_3634_,
                        v_a_3635_,
                        v_a_3636_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3666_) == 0 {
                    v_isSharedCheck_3676_ = (!crate::leanh::lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3676_ == 0 {
                        v_unused_3677_ = crate::leanh::lean_ctor_get(v___x_3666_, 0);
                        crate::leanh::lean_dec(v_unused_3677_);
                        v___x_3668_ = v___x_3666_;
                        v_isShared_3669_ = v_isSharedCheck_3676_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3666_);
                        v___x_3668_ = crate::leanh::lean_box(0);
                        v_isShared_3669_ = v_isSharedCheck_3676_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3657_);
                    crate::leanh::lean_dec(v_snd_3655_);
                    crate::leanh::lean_dec(v_fst_3646_);
                    v_a_3678_ = crate::leanh::lean_ctor_get(v___x_3666_, 0);
                    v_isSharedCheck_3685_ = (!crate::leanh::lean_is_exclusive(v___x_3666_)) as u8;
                    if v_isSharedCheck_3685_ == 0 {
                        v___x_3680_ = v___x_3666_;
                        v_isShared_3681_ = v_isSharedCheck_3685_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3678_);
                        crate::leanh::lean_dec(v___x_3666_);
                        v___x_3680_ = crate::leanh::lean_box(0);
                        v_isShared_3681_ = v_isSharedCheck_3685_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3657_, 0, v_fst_3646_);
                    v___x_3671_ = v___x_3657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_fst_3646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_snd_3655_);
                    v___x_3671_ = v_reuseFailAlloc_3675_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3669_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3668_, 0, v___x_3671_);
                    v___x_3673_ = v___x_3668_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
                    v___x_3673_ = v_reuseFailAlloc_3674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3673_;
            }
            5 => {
                if v_isShared_3681_ == 0 {
                    v___x_3683_ = v___x_3680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3683_;
            }
            7 => {
                if v_isShared_3690_ == 0 {
                    v___x_3692_ = v___x_3689_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
                    v___x_3692_ = v_reuseFailAlloc_3693_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3692_;
            }
            9 => {
                if v_isShared_3698_ == 0 {
                    v___x_3700_ = v___x_3697_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
                    v___x_3700_ = v_reuseFailAlloc_3701_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3700_;
            }
            11 => {
                if v_isShared_3706_ == 0 {
                    v___x_3708_ = v___x_3705_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
                    v___x_3708_ = v_reuseFailAlloc_3709_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withReverted___redArg___boxed(
    mut v_mvarId_3711_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3712_: *mut crate::leanh::LeanObject,
    mut v_k_3713_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_3720_: u8 = 0;
    let mut v_res_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clearAuxDeclsInsteadOfRevert_boxed_3720_ =
        (crate::leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_3714_) as u8);
    v_res_3721_ = l_Lean_MVarId_withReverted___redArg(
        v_mvarId_3711_,
        v_fvarIds_3712_,
        v_k_3713_,
        v_clearAuxDeclsInsteadOfRevert_boxed_3720_,
        v_a_3715_,
        v_a_3716_,
        v_a_3717_,
        v_a_3718_,
    );
    crate::leanh::lean_dec(v_a_3718_);
    crate::leanh::lean_dec_ref(v_a_3717_);
    crate::leanh::lean_dec(v_a_3716_);
    crate::leanh::lean_dec_ref(v_a_3715_);
    return v_res_3721_;
}
pub unsafe fn l_Lean_MVarId_withReverted(
    mut v_00_u03b1_3722_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3723_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3724_: *mut crate::leanh::LeanObject,
    mut v_k_3725_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_3726_: u8,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3732_ = l_Lean_MVarId_withReverted___redArg(
        v_mvarId_3723_,
        v_fvarIds_3724_,
        v_k_3725_,
        v_clearAuxDeclsInsteadOfRevert_3726_,
        v_a_3727_,
        v_a_3728_,
        v_a_3729_,
        v_a_3730_,
    );
    return v___x_3732_;
}
pub unsafe fn l_Lean_MVarId_withReverted___boxed(
    mut v_00_u03b1_3733_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3734_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3735_: *mut crate::leanh::LeanObject,
    mut v_k_3736_: *mut crate::leanh::LeanObject,
    mut v_clearAuxDeclsInsteadOfRevert_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clearAuxDeclsInsteadOfRevert_boxed_3743_: u8 = 0;
    let mut v_res_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clearAuxDeclsInsteadOfRevert_boxed_3743_ =
        (crate::leanh::lean_unbox(v_clearAuxDeclsInsteadOfRevert_3737_) as u8);
    v_res_3744_ = l_Lean_MVarId_withReverted(
        v_00_u03b1_3733_,
        v_mvarId_3734_,
        v_fvarIds_3735_,
        v_k_3736_,
        v_clearAuxDeclsInsteadOfRevert_boxed_3743_,
        v_a_3738_,
        v_a_3739_,
        v_a_3740_,
        v_a_3741_,
    );
    crate::leanh::lean_dec(v_a_3741_);
    crate::leanh::lean_dec_ref(v_a_3740_);
    crate::leanh::lean_dec(v_a_3739_);
    crate::leanh::lean_dec_ref(v_a_3738_);
    return v_res_3744_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(
    mut v_t_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___redArg(v_t_3745_, v___y_3749_);
    return v___x_3751_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0___boxed(
    mut v_t_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3758_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_MVarId_withReverted_spec__0_spec__0(v_t_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
    crate::leanh::lean_dec(v___y_3756_);
    crate::leanh::lean_dec_ref(v___y_3755_);
    crate::leanh::lean_dec(v___y_3754_);
    crate::leanh::lean_dec_ref(v___y_3753_);
    return v_res_3758_;
}
pub unsafe fn l_Lean_MVarId_withRevertedFrom___redArg(
    mut v_mvarId_3759_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3760_: *mut crate::leanh::LeanObject,
    mut v_k_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut v___x_3780_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3787_: u8 = 0;
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3791_: usize = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_unused_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v_a_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_a_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3767_ = l_Lean_MVarId_revertFrom(
                    v_mvarId_3759_,
                    v_fvarId_3760_,
                    v_a_3762_,
                    v_a_3763_,
                    v_a_3764_,
                    v_a_3765_,
                );
                if crate::leanh::lean_obj_tag(v___x_3767_) == 0 {
                    v_a_3768_ = crate::leanh::lean_ctor_get(v___x_3767_, 0);
                    crate::leanh::lean_inc(v_a_3768_);
                    crate::leanh::lean_dec_ref_known(v___x_3767_, 1);
                    v_fst_3769_ = crate::leanh::lean_ctor_get(v_a_3768_, 0);
                    crate::leanh::lean_inc(v_fst_3769_);
                    v_snd_3770_ = crate::leanh::lean_ctor_get(v_a_3768_, 1);
                    crate::leanh::lean_inc(v_snd_3770_);
                    crate::leanh::lean_dec(v_a_3768_);
                    crate::leanh::lean_inc(v_a_3765_);
                    crate::leanh::lean_inc_ref(v_a_3764_);
                    crate::leanh::lean_inc(v_a_3763_);
                    crate::leanh::lean_inc_ref(v_a_3762_);
                    v___x_3771_ = crate::leanh::lean_apply_7(
                        v_k_3761_,
                        v_snd_3770_,
                        v_fst_3769_,
                        v_a_3762_,
                        v_a_3763_,
                        v_a_3764_,
                        v_a_3765_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3771_) == 0 {
                        v_a_3772_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                        crate::leanh::lean_inc(v_a_3772_);
                        crate::leanh::lean_dec_ref_known(v___x_3771_, 1);
                        v_snd_3773_ = crate::leanh::lean_ctor_get(v_a_3772_, 1);
                        crate::leanh::lean_inc(v_snd_3773_);
                        v_fst_3774_ = crate::leanh::lean_ctor_get(v_a_3772_, 0);
                        crate::leanh::lean_inc(v_fst_3774_);
                        crate::leanh::lean_dec(v_a_3772_);
                        v_fst_3775_ = crate::leanh::lean_ctor_get(v_snd_3773_, 0);
                        crate::leanh::lean_inc(v_fst_3775_);
                        v_snd_3776_ = crate::leanh::lean_ctor_get(v_snd_3773_, 1);
                        crate::leanh::lean_inc(v_snd_3776_);
                        crate::leanh::lean_dec(v_snd_3773_);
                        v___x_3777_ = lean_array_get_size(v_fst_3775_);
                        v___x_3778_ = crate::leanh::lean_box(0);
                        v___x_3779_ = 0;
                        v___x_3780_ = 1;
                        v___x_3781_ = l_Lean_Meta_introNCore(
                            v_snd_3776_,
                            v___x_3777_,
                            v___x_3778_,
                            v___x_3779_,
                            v___x_3780_,
                            v_a_3762_,
                            v_a_3763_,
                            v_a_3764_,
                            v_a_3765_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3781_) == 0 {
                            v_a_3782_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                            crate::leanh::lean_inc(v_a_3782_);
                            crate::leanh::lean_dec_ref_known(v___x_3781_, 1);
                            v_fst_3783_ = crate::leanh::lean_ctor_get(v_a_3782_, 0);
                            v_snd_3784_ = crate::leanh::lean_ctor_get(v_a_3782_, 1);
                            v_isSharedCheck_3815_ =
                                (!crate::leanh::lean_is_exclusive(v_a_3782_)) as u8;
                            if v_isSharedCheck_3815_ == 0 {
                                v___x_3786_ = v_a_3782_;
                                v_isShared_3787_ = v_isSharedCheck_3815_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_3784_);
                                crate::leanh::lean_inc(v_fst_3783_);
                                crate::leanh::lean_dec(v_a_3782_);
                                v___x_3786_ = crate::leanh::lean_box(0);
                                v_isShared_3787_ = v_isSharedCheck_3815_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_3775_);
                            crate::leanh::lean_dec(v_fst_3774_);
                            v_a_3816_ = crate::leanh::lean_ctor_get(v___x_3781_, 0);
                            v_isSharedCheck_3823_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3781_)) as u8;
                            if v_isSharedCheck_3823_ == 0 {
                                v___x_3818_ = v___x_3781_;
                                v_isShared_3819_ = v_isSharedCheck_3823_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3816_);
                                crate::leanh::lean_dec(v___x_3781_);
                                v___x_3818_ = crate::leanh::lean_box(0);
                                v_isShared_3819_ = v_isSharedCheck_3823_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v_a_3824_ = crate::leanh::lean_ctor_get(v___x_3771_, 0);
                        v_isSharedCheck_3831_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3771_)) as u8;
                        if v_isSharedCheck_3831_ == 0 {
                            v___x_3826_ = v___x_3771_;
                            v_isShared_3827_ = v_isSharedCheck_3831_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3824_);
                            crate::leanh::lean_dec(v___x_3771_);
                            v___x_3826_ = crate::leanh::lean_box(0);
                            v_isShared_3827_ = v_isSharedCheck_3831_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_3761_);
                    v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3767_, 0);
                    v_isSharedCheck_3839_ = (!crate::leanh::lean_is_exclusive(v___x_3767_)) as u8;
                    if v_isSharedCheck_3839_ == 0 {
                        v___x_3834_ = v___x_3767_;
                        v_isShared_3835_ = v_isSharedCheck_3839_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3832_);
                        crate::leanh::lean_dec(v___x_3767_);
                        v___x_3834_ = crate::leanh::lean_box(0);
                        v_isShared_3835_ = v_isSharedCheck_3839_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3788_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3789_ = lean_array_get_size(v_fst_3783_);
                v___x_3790_ = l_Array_toSubarray___redArg(v_fst_3783_, v___x_3788_, v___x_3789_);
                v_sz_3791_ = lean_array_size(v_fst_3775_);
                v___x_3792_ = crate::leanh::lean_box_usize(v_sz_3791_);
                v___x_3793_ = l_Lean_MVarId_withReverted___redArg___boxed__const__1;
                v___f_3794_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MVarId_withReverted___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3794_, 0, v_fst_3775_);
                crate::leanh::lean_closure_set(v___f_3794_, 1, v___x_3792_);
                crate::leanh::lean_closure_set(v___f_3794_, 2, v___x_3793_);
                crate::leanh::lean_closure_set(v___f_3794_, 3, v___x_3790_);
                crate::leanh::lean_inc(v_snd_3784_);
                v___x_3795_ =
                    l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
                        v_snd_3784_,
                        v___f_3794_,
                        v_a_3762_,
                        v_a_3763_,
                        v_a_3764_,
                        v_a_3765_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3795_) == 0 {
                    v_isSharedCheck_3805_ = (!crate::leanh::lean_is_exclusive(v___x_3795_)) as u8;
                    if v_isSharedCheck_3805_ == 0 {
                        v_unused_3806_ = crate::leanh::lean_ctor_get(v___x_3795_, 0);
                        crate::leanh::lean_dec(v_unused_3806_);
                        v___x_3797_ = v___x_3795_;
                        v_isShared_3798_ = v_isSharedCheck_3805_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3795_);
                        v___x_3797_ = crate::leanh::lean_box(0);
                        v_isShared_3798_ = v_isSharedCheck_3805_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3786_);
                    crate::leanh::lean_dec(v_snd_3784_);
                    crate::leanh::lean_dec(v_fst_3774_);
                    v_a_3807_ = crate::leanh::lean_ctor_get(v___x_3795_, 0);
                    v_isSharedCheck_3814_ = (!crate::leanh::lean_is_exclusive(v___x_3795_)) as u8;
                    if v_isSharedCheck_3814_ == 0 {
                        v___x_3809_ = v___x_3795_;
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3807_);
                        crate::leanh::lean_dec(v___x_3795_);
                        v___x_3809_ = crate::leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3786_, 0, v_fst_3774_);
                    v___x_3800_ = v___x_3786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_fst_3774_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_snd_3784_);
                    v___x_3800_ = v_reuseFailAlloc_3804_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3797_, 0, v___x_3800_);
                    v___x_3802_ = v___x_3797_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
                    v___x_3802_ = v_reuseFailAlloc_3803_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3802_;
            }
            5 => {
                if v_isShared_3810_ == 0 {
                    v___x_3812_ = v___x_3809_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3812_;
            }
            7 => {
                if v_isShared_3819_ == 0 {
                    v___x_3821_ = v___x_3818_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
                    v___x_3821_ = v_reuseFailAlloc_3822_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3821_;
            }
            9 => {
                if v_isShared_3827_ == 0 {
                    v___x_3829_ = v___x_3826_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
                    v___x_3829_ = v_reuseFailAlloc_3830_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3829_;
            }
            11 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withRevertedFrom___redArg___boxed(
    mut v_mvarId_3840_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3841_: *mut crate::leanh::LeanObject,
    mut v_k_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
    mut v_a_3847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3848_ = l_Lean_MVarId_withRevertedFrom___redArg(
        v_mvarId_3840_,
        v_fvarId_3841_,
        v_k_3842_,
        v_a_3843_,
        v_a_3844_,
        v_a_3845_,
        v_a_3846_,
    );
    crate::leanh::lean_dec(v_a_3846_);
    crate::leanh::lean_dec_ref(v_a_3845_);
    crate::leanh::lean_dec(v_a_3844_);
    crate::leanh::lean_dec_ref(v_a_3843_);
    return v_res_3848_;
}
pub unsafe fn l_Lean_MVarId_withRevertedFrom(
    mut v_00_u03b1_3849_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3850_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3851_: *mut crate::leanh::LeanObject,
    mut v_k_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Lean_MVarId_withRevertedFrom___redArg(
        v_mvarId_3850_,
        v_fvarId_3851_,
        v_k_3852_,
        v_a_3853_,
        v_a_3854_,
        v_a_3855_,
        v_a_3856_,
    );
    return v___x_3858_;
}
pub unsafe fn l_Lean_MVarId_withRevertedFrom___boxed(
    mut v_00_u03b1_3859_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3860_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3861_: *mut crate::leanh::LeanObject,
    mut v_k_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_a_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_MVarId_withRevertedFrom(
        v_00_u03b1_3859_,
        v_mvarId_3860_,
        v_fvarId_3861_,
        v_k_3862_,
        v_a_3863_,
        v_a_3864_,
        v_a_3865_,
        v_a_3866_,
    );
    crate::leanh::lean_dec(v_a_3866_);
    crate::leanh::lean_dec_ref(v_a_3865_);
    crate::leanh::lean_dec(v_a_3864_);
    crate::leanh::lean_dec_ref(v_a_3863_);
    return v_res_3868_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__0(
    mut v_checkDefEq_3869_: u8,
    mut v_typeNew_3870_: *mut crate::leanh::LeanObject,
    mut v___x_3871_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3872_: *mut crate::leanh::LeanObject,
    mut v_typeOld_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3885_: u8 = 0;
    let mut v___x_3886_: u8 = 0;
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3900_: u8 = 0;
    let mut v_a_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_checkDefEq_3869_ == 0 {
                    crate::leanh::lean_dec_ref(v_typeOld_3873_);
                    crate::leanh::lean_dec(v_mvarId_3872_);
                    crate::leanh::lean_dec(v___x_3871_);
                    crate::leanh::lean_dec_ref(v_typeNew_3870_);
                    v___x_3879_ = crate::leanh::lean_box(0);
                    v___x_3880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3879_);
                    return v___x_3880_;
                } else {
                    crate::leanh::lean_inc_ref(v_typeOld_3873_);
                    crate::leanh::lean_inc_ref(v_typeNew_3870_);
                    v___x_3881_ = l_Lean_Meta_isExprDefEq(
                        v_typeNew_3870_,
                        v_typeOld_3873_,
                        v___y_3874_,
                        v___y_3875_,
                        v___y_3876_,
                        v___y_3877_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3881_) == 0 {
                        v_a_3882_ = crate::leanh::lean_ctor_get(v___x_3881_, 0);
                        v_isSharedCheck_3900_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3881_)) as u8;
                        if v_isSharedCheck_3900_ == 0 {
                            v___x_3884_ = v___x_3881_;
                            v_isShared_3885_ = v_isSharedCheck_3900_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3882_);
                            crate::leanh::lean_dec(v___x_3881_);
                            v___x_3884_ = crate::leanh::lean_box(0);
                            v_isShared_3885_ = v_isSharedCheck_3900_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_typeOld_3873_);
                        crate::leanh::lean_dec(v_mvarId_3872_);
                        crate::leanh::lean_dec(v___x_3871_);
                        crate::leanh::lean_dec_ref(v_typeNew_3870_);
                        v_a_3901_ = crate::leanh::lean_ctor_get(v___x_3881_, 0);
                        v_isSharedCheck_3908_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3881_)) as u8;
                        if v_isSharedCheck_3908_ == 0 {
                            v___x_3903_ = v___x_3881_;
                            v_isShared_3904_ = v_isSharedCheck_3908_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3901_);
                            crate::leanh::lean_dec(v___x_3881_);
                            v___x_3903_ = crate::leanh::lean_box(0);
                            v_isShared_3904_ = v_isSharedCheck_3908_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3886_ = (crate::leanh::lean_unbox(v_a_3882_) as u8);
                crate::leanh::lean_dec(v_a_3882_);
                if v___x_3886_ == 0 {
                    crate::leanh::lean_del_object(v___x_3884_);
                    v___x_3887_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_change___lam__0___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_change___lam__0___closed__1_once),
                        _init_l_Lean_MVarId_change___lam__0___closed__1,
                    );
                    v___x_3888_ = l_Lean_indentExpr(v_typeNew_3870_);
                    v___x_3889_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3889_, 0, v___x_3887_);
                    crate::leanh::lean_ctor_set(v___x_3889_, 1, v___x_3888_);
                    v___x_3890_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_change___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_change___lam__0___closed__3_once),
                        _init_l_Lean_MVarId_change___lam__0___closed__3,
                    );
                    v___x_3891_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3891_, 0, v___x_3889_);
                    crate::leanh::lean_ctor_set(v___x_3891_, 1, v___x_3890_);
                    v___x_3892_ = l_Lean_indentExpr(v_typeOld_3873_);
                    v___x_3893_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3893_, 0, v___x_3891_);
                    crate::leanh::lean_ctor_set(v___x_3893_, 1, v___x_3892_);
                    v___x_3894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3894_, 0, v___x_3893_);
                    v___x_3895_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3871_,
                        v_mvarId_3872_,
                        v___x_3894_,
                        v___y_3874_,
                        v___y_3875_,
                        v___y_3876_,
                        v___y_3877_,
                    );
                    return v___x_3895_;
                } else {
                    crate::leanh::lean_dec_ref(v_typeOld_3873_);
                    crate::leanh::lean_dec(v_mvarId_3872_);
                    crate::leanh::lean_dec(v___x_3871_);
                    crate::leanh::lean_dec_ref(v_typeNew_3870_);
                    v___x_3896_ = crate::leanh::lean_box(0);
                    if v_isShared_3885_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3884_, 0, v___x_3896_);
                        v___x_3898_ = v___x_3884_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
                        v___x_3898_ = v_reuseFailAlloc_3899_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3898_;
            }
            3 => {
                if v_isShared_3904_ == 0 {
                    v___x_3906_ = v___x_3903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__0___boxed(
    mut v_checkDefEq_3909_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3910_: *mut crate::leanh::LeanObject,
    mut v___x_3911_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3912_: *mut crate::leanh::LeanObject,
    mut v_typeOld_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkDefEq_boxed_3919_: u8 = 0;
    let mut v_res_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkDefEq_boxed_3919_ = (crate::leanh::lean_unbox(v_checkDefEq_3909_) as u8);
    v_res_3920_ = l_Lean_MVarId_changeLocalDecl___lam__0(
        v_checkDefEq_boxed_3919_,
        v_typeNew_3910_,
        v___x_3911_,
        v_mvarId_3912_,
        v_typeOld_3913_,
        v___y_3914_,
        v___y_3915_,
        v___y_3916_,
        v___y_3917_,
    );
    crate::leanh::lean_dec(v___y_3917_);
    crate::leanh::lean_dec_ref(v___y_3916_);
    crate::leanh::lean_dec(v___y_3915_);
    crate::leanh::lean_dec_ref(v___y_3914_);
    return v_res_3920_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(
    mut v_sz_3921_: usize,
    mut v_i_3922_: usize,
    mut v_bs_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: u8 = 0;
    let mut v_v_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: usize = 0;
    let mut v___x_3930_: usize = 0;
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3924_ = lean_usize_dec_lt(v_i_3922_, v_sz_3921_);
                if v___x_3924_ == 0 {
                    return v_bs_3923_;
                } else {
                    v_v_3925_ = lean_array_uget(v_bs_3923_, v_i_3922_);
                    v___x_3926_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3927_ = lean_array_uset(v_bs_3923_, v_i_3922_, v___x_3926_);
                    v___x_3928_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3928_, 0, v_v_3925_);
                    v___x_3929_ = 1usize;
                    v___x_3930_ = lean_usize_add(v_i_3922_, v___x_3929_);
                    v___x_3931_ = lean_array_uset(v_bs_x27_3927_, v_i_3922_, v___x_3928_);
                    v_i_3922_ = v___x_3930_;
                    v_bs_3923_ = v___x_3931_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0___boxed(
    mut v_sz_3933_: *mut crate::leanh::LeanObject,
    mut v_i_3934_: *mut crate::leanh::LeanObject,
    mut v_bs_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3936_: usize = 0;
    let mut v_i_boxed_3937_: usize = 0;
    let mut v_res_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3936_ = crate::leanh::lean_unbox_usize(v_sz_3933_);
    crate::leanh::lean_dec(v_sz_3933_);
    v_i_boxed_3937_ = crate::leanh::lean_unbox_usize(v_i_3934_);
    crate::leanh::lean_dec(v_i_3934_);
    v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_boxed_3936_, v_i_boxed_3937_, v_bs_3935_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__1(
    mut v_mvarId_3939_: *mut crate::leanh::LeanObject,
    mut v_fvars_3940_: *mut crate::leanh::LeanObject,
    mut v_targetNew_3941_: *mut crate::leanh::LeanObject,
    mut v___y_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3947_ = l_Lean_MVarId_replaceTargetDefEq(
                    v_mvarId_3939_,
                    v_targetNew_3941_,
                    v___y_3942_,
                    v___y_3943_,
                    v___y_3944_,
                    v___y_3945_,
                );
                if crate::leanh::lean_obj_tag(v___x_3947_) == 0 {
                    v_a_3948_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                    v_isSharedCheck_3961_ = (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3961_ == 0 {
                        v___x_3950_ = v___x_3947_;
                        v_isShared_3951_ = v_isSharedCheck_3961_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3948_);
                        crate::leanh::lean_dec(v___x_3947_);
                        v___x_3950_ = crate::leanh::lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3961_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fvars_3940_);
                    v_a_3962_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                    v_isSharedCheck_3969_ = (!crate::leanh::lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3969_ == 0 {
                        v___x_3964_ = v___x_3947_;
                        v_isShared_3965_ = v_isSharedCheck_3969_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3962_);
                        crate::leanh::lean_dec(v___x_3947_);
                        v___x_3964_ = crate::leanh::lean_box(0);
                        v_isShared_3965_ = v_isSharedCheck_3969_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3952_ = crate::leanh::lean_box(0);
                v_sz_3953_ = lean_array_size(v_fvars_3940_);
                v___x_3954_ = 0usize;
                v___x_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_3953_, v___x_3954_, v_fvars_3940_);
                v___x_3956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3955_);
                crate::leanh::lean_ctor_set(v___x_3956_, 1, v_a_3948_);
                v___x_3957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3952_);
                crate::leanh::lean_ctor_set(v___x_3957_, 1, v___x_3956_);
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3957_);
                    v___x_3959_ = v___x_3950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3957_);
                    v___x_3959_ = v_reuseFailAlloc_3960_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3959_;
            }
            3 => {
                if v_isShared_3965_ == 0 {
                    v___x_3967_ = v___x_3964_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
                    v___x_3967_ = v_reuseFailAlloc_3968_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__1___boxed(
    mut v_mvarId_3970_: *mut crate::leanh::LeanObject,
    mut v_fvars_3971_: *mut crate::leanh::LeanObject,
    mut v_targetNew_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3978_ = l_Lean_MVarId_changeLocalDecl___lam__1(
        v_mvarId_3970_,
        v_fvars_3971_,
        v_targetNew_3972_,
        v___y_3973_,
        v___y_3974_,
        v___y_3975_,
        v___y_3976_,
    );
    crate::leanh::lean_dec(v___y_3976_);
    crate::leanh::lean_dec_ref(v___y_3975_);
    crate::leanh::lean_dec(v___y_3974_);
    crate::leanh::lean_dec_ref(v___y_3973_);
    return v_res_3978_;
}
pub unsafe fn _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_Lean_MVarId_changeLocalDecl___lam__2___closed__1;
    v___x_3983_ = l_Lean_MessageData_ofFormat(v___x_3982_);
    return v___x_3983_;
}
pub unsafe fn _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3984_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_changeLocalDecl___lam__2___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_changeLocalDecl___lam__2___closed__2_once),
        _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__2,
    );
    v___x_3985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3985_, 0, v___x_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__2(
    mut v_mvarId_3986_: *mut crate::leanh::LeanObject,
    mut v___f_3987_: *mut crate::leanh::LeanObject,
    mut v_typeNew_3988_: *mut crate::leanh::LeanObject,
    mut v___f_3989_: *mut crate::leanh::LeanObject,
    mut v___x_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4001_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_declName_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4028_: u8 = 0;
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_3986_);
                v___x_3996_ = l_Lean_MVarId_getType(
                    v_mvarId_3986_,
                    v___y_3991_,
                    v___y_3992_,
                    v___y_3993_,
                    v___y_3994_,
                );
                if crate::leanh::lean_obj_tag(v___x_3996_) == 0 {
                    v_a_3997_ = crate::leanh::lean_ctor_get(v___x_3996_, 0);
                    crate::leanh::lean_inc(v_a_3997_);
                    crate::leanh::lean_dec_ref_known(v___x_3996_, 1);
                    match crate::leanh::lean_obj_tag(v_a_3997_) {
                        7 => {
                            crate::leanh::lean_dec(v___x_3990_);
                            crate::leanh::lean_dec(v_mvarId_3986_);
                            v_binderName_3998_ = crate::leanh::lean_ctor_get(v_a_3997_, 0);
                            crate::leanh::lean_inc(v_binderName_3998_);
                            v_binderType_3999_ = crate::leanh::lean_ctor_get(v_a_3997_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_3999_);
                            v_body_4000_ = crate::leanh::lean_ctor_get(v_a_3997_, 2);
                            crate::leanh::lean_inc_ref(v_body_4000_);
                            v_binderInfo_4001_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_3997_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_a_3997_, 3);
                            crate::leanh::lean_inc(v___y_3994_);
                            crate::leanh::lean_inc_ref(v___y_3993_);
                            crate::leanh::lean_inc(v___y_3992_);
                            crate::leanh::lean_inc_ref(v___y_3991_);
                            v___x_4002_ = crate::leanh::lean_apply_6(
                                v___f_3987_,
                                v_binderType_3999_,
                                v___y_3991_,
                                v___y_3992_,
                                v___y_3993_,
                                v___y_3994_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4002_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4002_, 1);
                                v___x_4003_ = l_Lean_Expr_forallE___override(
                                    v_binderName_3998_,
                                    v_typeNew_3988_,
                                    v_body_4000_,
                                    v_binderInfo_4001_,
                                );
                                v___x_4004_ = crate::leanh::lean_apply_6(
                                    v___f_3989_,
                                    v___x_4003_,
                                    v___y_3991_,
                                    v___y_3992_,
                                    v___y_3993_,
                                    v___y_3994_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_4004_;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4000_);
                                crate::leanh::lean_dec(v_binderName_3998_);
                                crate::leanh::lean_dec(v___y_3994_);
                                crate::leanh::lean_dec_ref(v___y_3993_);
                                crate::leanh::lean_dec(v___y_3992_);
                                crate::leanh::lean_dec_ref(v___y_3991_);
                                crate::leanh::lean_dec_ref(v___f_3989_);
                                crate::leanh::lean_dec_ref(v_typeNew_3988_);
                                v_a_4005_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
                                v_isSharedCheck_4012_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4002_)) as u8;
                                if v_isSharedCheck_4012_ == 0 {
                                    v___x_4007_ = v___x_4002_;
                                    v_isShared_4008_ = v_isSharedCheck_4012_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4005_);
                                    crate::leanh::lean_dec(v___x_4002_);
                                    v___x_4007_ = crate::leanh::lean_box(0);
                                    v_isShared_4008_ = v_isSharedCheck_4012_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        8 => {
                            crate::leanh::lean_dec(v___x_3990_);
                            crate::leanh::lean_dec(v_mvarId_3986_);
                            v_declName_4013_ = crate::leanh::lean_ctor_get(v_a_3997_, 0);
                            crate::leanh::lean_inc(v_declName_4013_);
                            v_type_4014_ = crate::leanh::lean_ctor_get(v_a_3997_, 1);
                            crate::leanh::lean_inc_ref(v_type_4014_);
                            v_value_4015_ = crate::leanh::lean_ctor_get(v_a_3997_, 2);
                            crate::leanh::lean_inc_ref(v_value_4015_);
                            v_body_4016_ = crate::leanh::lean_ctor_get(v_a_3997_, 3);
                            crate::leanh::lean_inc_ref(v_body_4016_);
                            v_nondep_4017_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_3997_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_a_3997_, 4);
                            crate::leanh::lean_inc(v___y_3994_);
                            crate::leanh::lean_inc_ref(v___y_3993_);
                            crate::leanh::lean_inc(v___y_3992_);
                            crate::leanh::lean_inc_ref(v___y_3991_);
                            v___x_4018_ = crate::leanh::lean_apply_6(
                                v___f_3987_,
                                v_type_4014_,
                                v___y_3991_,
                                v___y_3992_,
                                v___y_3993_,
                                v___y_3994_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_4018_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4018_, 1);
                                v___x_4019_ = l_Lean_Expr_letE___override(
                                    v_declName_4013_,
                                    v_typeNew_3988_,
                                    v_value_4015_,
                                    v_body_4016_,
                                    v_nondep_4017_,
                                );
                                v___x_4020_ = crate::leanh::lean_apply_6(
                                    v___f_3989_,
                                    v___x_4019_,
                                    v___y_3991_,
                                    v___y_3992_,
                                    v___y_3993_,
                                    v___y_3994_,
                                    crate::leanh::lean_box(0),
                                );
                                return v___x_4020_;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4016_);
                                crate::leanh::lean_dec_ref(v_value_4015_);
                                crate::leanh::lean_dec(v_declName_4013_);
                                crate::leanh::lean_dec(v___y_3994_);
                                crate::leanh::lean_dec_ref(v___y_3993_);
                                crate::leanh::lean_dec(v___y_3992_);
                                crate::leanh::lean_dec_ref(v___y_3991_);
                                crate::leanh::lean_dec_ref(v___f_3989_);
                                crate::leanh::lean_dec_ref(v_typeNew_3988_);
                                v_a_4021_ = crate::leanh::lean_ctor_get(v___x_4018_, 0);
                                v_isSharedCheck_4028_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4018_)) as u8;
                                if v_isSharedCheck_4028_ == 0 {
                                    v___x_4023_ = v___x_4018_;
                                    v_isShared_4024_ = v_isSharedCheck_4028_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4021_);
                                    crate::leanh::lean_dec(v___x_4018_);
                                    v___x_4023_ = crate::leanh::lean_box(0);
                                    v_isShared_4024_ = v_isSharedCheck_4028_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_a_3997_);
                            crate::leanh::lean_dec_ref(v___f_3989_);
                            crate::leanh::lean_dec_ref(v_typeNew_3988_);
                            crate::leanh::lean_dec_ref(v___f_3987_);
                            v___x_4029_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_changeLocalDecl___lam__2___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_changeLocalDecl___lam__2___closed__3_once
                                ),
                                _init_l_Lean_MVarId_changeLocalDecl___lam__2___closed__3,
                            );
                            v___x_4030_ = l_Lean_Meta_throwTacticEx___redArg(
                                v___x_3990_,
                                v_mvarId_3986_,
                                v___x_4029_,
                                v___y_3991_,
                                v___y_3992_,
                                v___y_3993_,
                                v___y_3994_,
                            );
                            crate::leanh::lean_dec(v___y_3994_);
                            crate::leanh::lean_dec_ref(v___y_3993_);
                            crate::leanh::lean_dec(v___y_3992_);
                            crate::leanh::lean_dec_ref(v___y_3991_);
                            return v___x_4030_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3994_);
                    crate::leanh::lean_dec_ref(v___y_3993_);
                    crate::leanh::lean_dec(v___y_3992_);
                    crate::leanh::lean_dec_ref(v___y_3991_);
                    crate::leanh::lean_dec(v___x_3990_);
                    crate::leanh::lean_dec_ref(v___f_3989_);
                    crate::leanh::lean_dec_ref(v_typeNew_3988_);
                    crate::leanh::lean_dec_ref(v___f_3987_);
                    crate::leanh::lean_dec(v_mvarId_3986_);
                    v_a_4031_ = crate::leanh::lean_ctor_get(v___x_3996_, 0);
                    v_isSharedCheck_4038_ = (!crate::leanh::lean_is_exclusive(v___x_3996_)) as u8;
                    if v_isSharedCheck_4038_ == 0 {
                        v___x_4033_ = v___x_3996_;
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4031_);
                        crate::leanh::lean_dec(v___x_3996_);
                        v___x_4033_ = crate::leanh::lean_box(0);
                        v_isShared_4034_ = v_isSharedCheck_4038_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4008_ == 0 {
                    v___x_4010_ = v___x_4007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4010_;
            }
            3 => {
                if v_isShared_4024_ == 0 {
                    v___x_4026_ = v___x_4023_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
                    v___x_4026_ = v_reuseFailAlloc_4027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4026_;
            }
            5 => {
                if v_isShared_4034_ == 0 {
                    v___x_4036_ = v___x_4033_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
                    v___x_4036_ = v_reuseFailAlloc_4037_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__2___boxed(
    mut v_mvarId_4039_: *mut crate::leanh::LeanObject,
    mut v___f_4040_: *mut crate::leanh::LeanObject,
    mut v_typeNew_4041_: *mut crate::leanh::LeanObject,
    mut v___f_4042_: *mut crate::leanh::LeanObject,
    mut v___x_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4049_ = l_Lean_MVarId_changeLocalDecl___lam__2(
        v_mvarId_4039_,
        v___f_4040_,
        v_typeNew_4041_,
        v___f_4042_,
        v___x_4043_,
        v___y_4044_,
        v___y_4045_,
        v___y_4046_,
        v___y_4047_,
    );
    return v_res_4049_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__3(
    mut v_checkDefEq_4050_: u8,
    mut v_typeNew_4051_: *mut crate::leanh::LeanObject,
    mut v___x_4052_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4053_: *mut crate::leanh::LeanObject,
    mut v_fvars_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ = crate::leanh::lean_box((v_checkDefEq_4050_) as usize);
    crate::leanh::lean_inc_n(v_mvarId_4053_, 3);
    crate::leanh::lean_inc(v___x_4052_);
    crate::leanh::lean_inc_ref(v_typeNew_4051_);
    v___f_4061_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_changeLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4061_, 0, v___x_4060_);
    crate::leanh::lean_closure_set(v___f_4061_, 1, v_typeNew_4051_);
    crate::leanh::lean_closure_set(v___f_4061_, 2, v___x_4052_);
    crate::leanh::lean_closure_set(v___f_4061_, 3, v_mvarId_4053_);
    v___f_4062_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_changeLocalDecl___lam__1___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4062_, 0, v_mvarId_4053_);
    crate::leanh::lean_closure_set(v___f_4062_, 1, v_fvars_4054_);
    v___f_4063_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_changeLocalDecl___lam__2___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_4063_, 0, v_mvarId_4053_);
    crate::leanh::lean_closure_set(v___f_4063_, 1, v___f_4061_);
    crate::leanh::lean_closure_set(v___f_4063_, 2, v_typeNew_4051_);
    crate::leanh::lean_closure_set(v___f_4063_, 3, v___f_4062_);
    crate::leanh::lean_closure_set(v___f_4063_, 4, v___x_4052_);
    v___x_4064_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_4053_,
        v___f_4063_,
        v___y_4055_,
        v___y_4056_,
        v___y_4057_,
        v___y_4058_,
    );
    return v___x_4064_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___lam__3___boxed(
    mut v_checkDefEq_4065_: *mut crate::leanh::LeanObject,
    mut v_typeNew_4066_: *mut crate::leanh::LeanObject,
    mut v___x_4067_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4068_: *mut crate::leanh::LeanObject,
    mut v_fvars_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkDefEq_boxed_4075_: u8 = 0;
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkDefEq_boxed_4075_ = (crate::leanh::lean_unbox(v_checkDefEq_4065_) as u8);
    v_res_4076_ = l_Lean_MVarId_changeLocalDecl___lam__3(
        v_checkDefEq_boxed_4075_,
        v_typeNew_4066_,
        v___x_4067_,
        v_mvarId_4068_,
        v_fvars_4069_,
        v___y_4070_,
        v___y_4071_,
        v___y_4072_,
        v___y_4073_,
    );
    crate::leanh::lean_dec(v___y_4073_);
    crate::leanh::lean_dec_ref(v___y_4072_);
    crate::leanh::lean_dec(v___y_4071_);
    crate::leanh::lean_dec_ref(v___y_4070_);
    return v_res_4076_;
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl(
    mut v_mvarId_4080_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4081_: *mut crate::leanh::LeanObject,
    mut v_typeNew_4082_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_4083_: u8,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v_snd_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_a_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_a_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4089_ = l_Lean_MVarId_changeLocalDecl___closed__1;
                crate::leanh::lean_inc(v_mvarId_4080_);
                v___x_4090_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4080_,
                    v___x_4089_,
                    v_a_4084_,
                    v_a_4085_,
                    v_a_4086_,
                    v_a_4087_,
                );
                if crate::leanh::lean_obj_tag(v___x_4090_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4090_, 1);
                    v___x_4091_ = crate::leanh::lean_box((v_checkDefEq_4083_) as usize);
                    v___f_4092_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_changeLocalDecl___lam__3___boxed as *mut core::ffi::c_void,
                        10,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_4092_, 0, v___x_4091_);
                    crate::leanh::lean_closure_set(v___f_4092_, 1, v_typeNew_4082_);
                    crate::leanh::lean_closure_set(v___f_4092_, 2, v___x_4089_);
                    v___x_4093_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4094_ = lean_mk_empty_array_with_capacity(v___x_4093_);
                    v___x_4095_ = lean_array_push(v___x_4094_, v_fvarId_4081_);
                    v___x_4096_ = 0;
                    v___x_4097_ = l_Lean_MVarId_withReverted___redArg(
                        v_mvarId_4080_,
                        v___x_4095_,
                        v___f_4092_,
                        v___x_4096_,
                        v_a_4084_,
                        v_a_4085_,
                        v_a_4086_,
                        v_a_4087_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4097_) == 0 {
                        v_a_4098_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
                        v_isSharedCheck_4106_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4097_)) as u8;
                        if v_isSharedCheck_4106_ == 0 {
                            v___x_4100_ = v___x_4097_;
                            v_isShared_4101_ = v_isSharedCheck_4106_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4098_);
                            crate::leanh::lean_dec(v___x_4097_);
                            v___x_4100_ = crate::leanh::lean_box(0);
                            v_isShared_4101_ = v_isSharedCheck_4106_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4107_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
                        v_isSharedCheck_4114_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4097_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4109_ = v___x_4097_;
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4107_);
                            crate::leanh::lean_dec(v___x_4097_);
                            v___x_4109_ = crate::leanh::lean_box(0);
                            v_isShared_4110_ = v_isSharedCheck_4114_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_typeNew_4082_);
                    crate::leanh::lean_dec(v_fvarId_4081_);
                    crate::leanh::lean_dec(v_mvarId_4080_);
                    v_a_4115_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
                    v_isSharedCheck_4122_ = (!crate::leanh::lean_is_exclusive(v___x_4090_)) as u8;
                    if v_isSharedCheck_4122_ == 0 {
                        v___x_4117_ = v___x_4090_;
                        v_isShared_4118_ = v_isSharedCheck_4122_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4115_);
                        crate::leanh::lean_dec(v___x_4090_);
                        v___x_4117_ = crate::leanh::lean_box(0);
                        v_isShared_4118_ = v_isSharedCheck_4122_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4102_ = crate::leanh::lean_ctor_get(v_a_4098_, 1);
                crate::leanh::lean_inc(v_snd_4102_);
                crate::leanh::lean_dec(v_a_4098_);
                if v_isShared_4101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4100_, 0, v_snd_4102_);
                    v___x_4104_ = v___x_4100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_snd_4102_);
                    v___x_4104_ = v_reuseFailAlloc_4105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4104_;
            }
            3 => {
                if v_isShared_4110_ == 0 {
                    v___x_4112_ = v___x_4109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_a_4107_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4112_;
            }
            5 => {
                if v_isShared_4118_ == 0 {
                    v___x_4120_ = v___x_4117_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
                    v___x_4120_ = v_reuseFailAlloc_4121_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_changeLocalDecl___boxed(
    mut v_mvarId_4123_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4124_: *mut crate::leanh::LeanObject,
    mut v_typeNew_4125_: *mut crate::leanh::LeanObject,
    mut v_checkDefEq_4126_: *mut crate::leanh::LeanObject,
    mut v_a_4127_: *mut crate::leanh::LeanObject,
    mut v_a_4128_: *mut crate::leanh::LeanObject,
    mut v_a_4129_: *mut crate::leanh::LeanObject,
    mut v_a_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checkDefEq_boxed_4132_: u8 = 0;
    let mut v_res_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_checkDefEq_boxed_4132_ = (crate::leanh::lean_unbox(v_checkDefEq_4126_) as u8);
    v_res_4133_ = l_Lean_MVarId_changeLocalDecl(
        v_mvarId_4123_,
        v_fvarId_4124_,
        v_typeNew_4125_,
        v_checkDefEq_boxed_4132_,
        v_a_4127_,
        v_a_4128_,
        v_a_4129_,
        v_a_4130_,
    );
    crate::leanh::lean_dec(v_a_4130_);
    crate::leanh::lean_dec_ref(v_a_4129_);
    crate::leanh::lean_dec(v_a_4128_);
    crate::leanh::lean_dec_ref(v_a_4127_);
    return v_res_4133_;
}
pub unsafe fn l_Lean_MVarId_modifyTarget___lam__0(
    mut v_mvarId_4134_: *mut crate::leanh::LeanObject,
    mut v___x_4135_: *mut crate::leanh::LeanObject,
    mut v_f_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_a_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_4134_);
                v___x_4142_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4134_,
                    v___x_4135_,
                    v___y_4137_,
                    v___y_4138_,
                    v___y_4139_,
                    v___y_4140_,
                );
                if crate::leanh::lean_obj_tag(v___x_4142_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4142_, 1);
                    crate::leanh::lean_inc(v_mvarId_4134_);
                    v___x_4143_ = l_Lean_MVarId_getType(
                        v_mvarId_4134_,
                        v___y_4137_,
                        v___y_4138_,
                        v___y_4139_,
                        v___y_4140_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4143_) == 0 {
                        v_a_4144_ = crate::leanh::lean_ctor_get(v___x_4143_, 0);
                        crate::leanh::lean_inc(v_a_4144_);
                        crate::leanh::lean_dec_ref_known(v___x_4143_, 1);
                        crate::leanh::lean_inc(v___y_4140_);
                        crate::leanh::lean_inc_ref(v___y_4139_);
                        crate::leanh::lean_inc(v___y_4138_);
                        crate::leanh::lean_inc_ref(v___y_4137_);
                        v___x_4145_ = crate::leanh::lean_apply_6(
                            v_f_4136_,
                            v_a_4144_,
                            v___y_4137_,
                            v___y_4138_,
                            v___y_4139_,
                            v___y_4140_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4145_) == 0 {
                            v_a_4146_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                            crate::leanh::lean_inc(v_a_4146_);
                            crate::leanh::lean_dec_ref_known(v___x_4145_, 1);
                            v___x_4147_ = 0;
                            v___x_4148_ = l_Lean_MVarId_change(
                                v_mvarId_4134_,
                                v_a_4146_,
                                v___x_4147_,
                                v___y_4137_,
                                v___y_4138_,
                                v___y_4139_,
                                v___y_4140_,
                            );
                            crate::leanh::lean_dec(v___y_4140_);
                            crate::leanh::lean_dec_ref(v___y_4139_);
                            crate::leanh::lean_dec(v___y_4138_);
                            crate::leanh::lean_dec_ref(v___y_4137_);
                            return v___x_4148_;
                        } else {
                            crate::leanh::lean_dec(v___y_4140_);
                            crate::leanh::lean_dec_ref(v___y_4139_);
                            crate::leanh::lean_dec(v___y_4138_);
                            crate::leanh::lean_dec_ref(v___y_4137_);
                            crate::leanh::lean_dec(v_mvarId_4134_);
                            v_a_4149_ = crate::leanh::lean_ctor_get(v___x_4145_, 0);
                            v_isSharedCheck_4156_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4145_)) as u8;
                            if v_isSharedCheck_4156_ == 0 {
                                v___x_4151_ = v___x_4145_;
                                v_isShared_4152_ = v_isSharedCheck_4156_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4149_);
                                crate::leanh::lean_dec(v___x_4145_);
                                v___x_4151_ = crate::leanh::lean_box(0);
                                v_isShared_4152_ = v_isSharedCheck_4156_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4140_);
                        crate::leanh::lean_dec_ref(v___y_4139_);
                        crate::leanh::lean_dec(v___y_4138_);
                        crate::leanh::lean_dec_ref(v___y_4137_);
                        crate::leanh::lean_dec_ref(v_f_4136_);
                        crate::leanh::lean_dec(v_mvarId_4134_);
                        v_a_4157_ = crate::leanh::lean_ctor_get(v___x_4143_, 0);
                        v_isSharedCheck_4164_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4143_)) as u8;
                        if v_isSharedCheck_4164_ == 0 {
                            v___x_4159_ = v___x_4143_;
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4157_);
                            crate::leanh::lean_dec(v___x_4143_);
                            v___x_4159_ = crate::leanh::lean_box(0);
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4140_);
                    crate::leanh::lean_dec_ref(v___y_4139_);
                    crate::leanh::lean_dec(v___y_4138_);
                    crate::leanh::lean_dec_ref(v___y_4137_);
                    crate::leanh::lean_dec_ref(v_f_4136_);
                    crate::leanh::lean_dec(v_mvarId_4134_);
                    v_a_4165_ = crate::leanh::lean_ctor_get(v___x_4142_, 0);
                    v_isSharedCheck_4172_ = (!crate::leanh::lean_is_exclusive(v___x_4142_)) as u8;
                    if v_isSharedCheck_4172_ == 0 {
                        v___x_4167_ = v___x_4142_;
                        v_isShared_4168_ = v_isSharedCheck_4172_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4165_);
                        crate::leanh::lean_dec(v___x_4142_);
                        v___x_4167_ = crate::leanh::lean_box(0);
                        v_isShared_4168_ = v_isSharedCheck_4172_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4154_;
            }
            3 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4162_;
            }
            5 => {
                if v_isShared_4168_ == 0 {
                    v___x_4170_ = v___x_4167_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
                    v___x_4170_ = v_reuseFailAlloc_4171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_modifyTarget___lam__0___boxed(
    mut v_mvarId_4173_: *mut crate::leanh::LeanObject,
    mut v___x_4174_: *mut crate::leanh::LeanObject,
    mut v_f_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lean_MVarId_modifyTarget___lam__0(
        v_mvarId_4173_,
        v___x_4174_,
        v_f_4175_,
        v___y_4176_,
        v___y_4177_,
        v___y_4178_,
        v___y_4179_,
    );
    return v_res_4181_;
}
pub unsafe fn l_Lean_MVarId_modifyTarget(
    mut v_mvarId_4185_: *mut crate::leanh::LeanObject,
    mut v_f_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
    mut v_a_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4192_ = l_Lean_MVarId_modifyTarget___closed__1;
    crate::leanh::lean_inc(v_mvarId_4185_);
    v___f_4193_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_modifyTarget___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4193_, 0, v_mvarId_4185_);
    crate::leanh::lean_closure_set(v___f_4193_, 1, v___x_4192_);
    crate::leanh::lean_closure_set(v___f_4193_, 2, v_f_4186_);
    v___x_4194_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_4185_,
        v___f_4193_,
        v_a_4187_,
        v_a_4188_,
        v_a_4189_,
        v_a_4190_,
    );
    return v___x_4194_;
}
pub unsafe fn l_Lean_MVarId_modifyTarget___boxed(
    mut v_mvarId_4195_: *mut crate::leanh::LeanObject,
    mut v_f_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_MVarId_modifyTarget(
        v_mvarId_4195_,
        v_f_4196_,
        v_a_4197_,
        v_a_4198_,
        v_a_4199_,
        v_a_4200_,
    );
    crate::leanh::lean_dec(v_a_4200_);
    crate::leanh::lean_dec_ref(v_a_4199_);
    crate::leanh::lean_dec(v_a_4198_);
    crate::leanh::lean_dec_ref(v_a_4197_);
    return v_res_4202_;
}
pub unsafe fn _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__2;
    v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn l_Lean_MVarId_modifyTargetEqLHS___lam__0(
    mut v_f_4209_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4210_: *mut crate::leanh::LeanObject,
    mut v_target_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
    mut v___y_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4235_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_target_4211_);
                v___x_4217_ = l_Lean_Meta_matchEq_x3f(
                    v_target_4211_,
                    v___y_4212_,
                    v___y_4213_,
                    v___y_4214_,
                    v___y_4215_,
                );
                if crate::leanh::lean_obj_tag(v___x_4217_) == 0 {
                    v_a_4218_ = crate::leanh::lean_ctor_get(v___x_4217_, 0);
                    crate::leanh::lean_inc(v_a_4218_);
                    crate::leanh::lean_dec_ref_known(v___x_4217_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4218_) == 1 {
                        crate::leanh::lean_dec_ref(v_target_4211_);
                        crate::leanh::lean_dec(v_mvarId_4210_);
                        v_val_4219_ = crate::leanh::lean_ctor_get(v_a_4218_, 0);
                        crate::leanh::lean_inc(v_val_4219_);
                        crate::leanh::lean_dec_ref_known(v_a_4218_, 1);
                        v_snd_4220_ = crate::leanh::lean_ctor_get(v_val_4219_, 1);
                        crate::leanh::lean_inc(v_snd_4220_);
                        crate::leanh::lean_dec(v_val_4219_);
                        v_fst_4221_ = crate::leanh::lean_ctor_get(v_snd_4220_, 0);
                        crate::leanh::lean_inc(v_fst_4221_);
                        v_snd_4222_ = crate::leanh::lean_ctor_get(v_snd_4220_, 1);
                        crate::leanh::lean_inc(v_snd_4222_);
                        crate::leanh::lean_dec(v_snd_4220_);
                        crate::leanh::lean_inc(v___y_4215_);
                        crate::leanh::lean_inc_ref(v___y_4214_);
                        crate::leanh::lean_inc(v___y_4213_);
                        crate::leanh::lean_inc_ref(v___y_4212_);
                        v___x_4223_ = crate::leanh::lean_apply_6(
                            v_f_4209_,
                            v_fst_4221_,
                            v___y_4212_,
                            v___y_4213_,
                            v___y_4214_,
                            v___y_4215_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_4223_) == 0 {
                            v_a_4224_ = crate::leanh::lean_ctor_get(v___x_4223_, 0);
                            crate::leanh::lean_inc(v_a_4224_);
                            crate::leanh::lean_dec_ref_known(v___x_4223_, 1);
                            v___x_4225_ = l_Lean_Meta_mkEq(
                                v_a_4224_,
                                v_snd_4222_,
                                v___y_4212_,
                                v___y_4213_,
                                v___y_4214_,
                                v___y_4215_,
                            );
                            return v___x_4225_;
                        } else {
                            crate::leanh::lean_dec(v_snd_4222_);
                            return v___x_4223_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4218_);
                        crate::leanh::lean_dec_ref(v_f_4209_);
                        v___x_4226_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__1;
                        v___x_4227_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3_once
                            ),
                            _init_l_Lean_MVarId_modifyTargetEqLHS___lam__0___closed__3,
                        );
                        v___x_4228_ = l_Lean_indentExpr(v_target_4211_);
                        v___x_4229_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4229_, 0, v___x_4227_);
                        crate::leanh::lean_ctor_set(v___x_4229_, 1, v___x_4228_);
                        v___x_4230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4230_, 0, v___x_4229_);
                        v___x_4231_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_4226_,
                            v_mvarId_4210_,
                            v___x_4230_,
                            v___y_4212_,
                            v___y_4213_,
                            v___y_4214_,
                            v___y_4215_,
                        );
                        return v___x_4231_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_target_4211_);
                    crate::leanh::lean_dec(v_mvarId_4210_);
                    crate::leanh::lean_dec_ref(v_f_4209_);
                    v_a_4232_ = crate::leanh::lean_ctor_get(v___x_4217_, 0);
                    v_isSharedCheck_4239_ = (!crate::leanh::lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4239_ == 0 {
                        v___x_4234_ = v___x_4217_;
                        v_isShared_4235_ = v_isSharedCheck_4239_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4232_);
                        crate::leanh::lean_dec(v___x_4217_);
                        v___x_4234_ = crate::leanh::lean_box(0);
                        v_isShared_4235_ = v_isSharedCheck_4239_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4235_ == 0 {
                    v___x_4237_ = v___x_4234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed(
    mut v_f_4240_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4241_: *mut crate::leanh::LeanObject,
    mut v_target_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lean_MVarId_modifyTargetEqLHS___lam__0(
        v_f_4240_,
        v_mvarId_4241_,
        v_target_4242_,
        v___y_4243_,
        v___y_4244_,
        v___y_4245_,
        v___y_4246_,
    );
    crate::leanh::lean_dec(v___y_4246_);
    crate::leanh::lean_dec_ref(v___y_4245_);
    crate::leanh::lean_dec(v___y_4244_);
    crate::leanh::lean_dec_ref(v___y_4243_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_MVarId_modifyTargetEqLHS(
    mut v_mvarId_4249_: *mut crate::leanh::LeanObject,
    mut v_f_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_4249_);
    v___f_4256_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_modifyTargetEqLHS___lam__0___boxed as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4256_, 0, v_f_4250_);
    crate::leanh::lean_closure_set(v___f_4256_, 1, v_mvarId_4249_);
    v___x_4257_ = l_Lean_MVarId_modifyTarget(
        v_mvarId_4249_,
        v___f_4256_,
        v_a_4251_,
        v_a_4252_,
        v_a_4253_,
        v_a_4254_,
    );
    return v___x_4257_;
}
pub unsafe fn l_Lean_MVarId_modifyTargetEqLHS___boxed(
    mut v_mvarId_4258_: *mut crate::leanh::LeanObject,
    mut v_f_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4265_ = l_Lean_MVarId_modifyTargetEqLHS(
        v_mvarId_4258_,
        v_f_4259_,
        v_a_4260_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
    );
    crate::leanh::lean_dec(v_a_4263_);
    crate::leanh::lean_dec_ref(v_a_4262_);
    crate::leanh::lean_dec(v_a_4261_);
    crate::leanh::lean_dec_ref(v_a_4260_);
    return v_res_4265_;
}
pub unsafe fn _init_l_Lean_MVarId_clearValue___lam__0___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = l_Lean_MVarId_clearValue___lam__0___closed__0;
    v___x_4268_ = l_Lean_stringToMessageData(v___x_4267_);
    return v___x_4268_;
}
pub unsafe fn _init_l_Lean_MVarId_clearValue___lam__0___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4270_ = l_Lean_MVarId_clearValue___lam__0___closed__2;
    v___x_4271_ = l_Lean_stringToMessageData(v___x_4270_);
    return v___x_4271_;
}
pub unsafe fn _init_l_Lean_MVarId_clearValue___lam__0___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4273_ = l_Lean_MVarId_clearValue___lam__0___closed__4;
    v___x_4274_ = l_Lean_stringToMessageData(v___x_4273_);
    return v___x_4274_;
}
pub unsafe fn _init_l_Lean_MVarId_clearValue___lam__0___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4276_ = l_Lean_MVarId_clearValue___lam__0___closed__6;
    v___x_4277_ = l_Lean_stringToMessageData(v___x_4276_);
    return v___x_4277_;
}
pub unsafe fn l_Lean_MVarId_clearValue___lam__0(
    mut v_mvarId_x27_4278_: *mut crate::leanh::LeanObject,
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_fvars_4280_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4281_: *mut crate::leanh::LeanObject,
    mut v___x_4282_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4304_: u8 = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4306_: usize = 0;
    let mut v___x_4307_: usize = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4315_: u8 = 0;
    let mut v_unused_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v___y_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4339_: u8 = 0;
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4360_: u8 = 0;
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_a_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_x27_4278_);
                v___x_4289_ = l_Lean_MVarId_getType(
                    v_mvarId_x27_4278_,
                    v___y_4284_,
                    v___y_4285_,
                    v___y_4286_,
                    v___y_4287_,
                );
                if crate::leanh::lean_obj_tag(v___x_4289_) == 0 {
                    v_a_4290_ = crate::leanh::lean_ctor_get(v___x_4289_, 0);
                    crate::leanh::lean_inc(v_a_4290_);
                    crate::leanh::lean_dec_ref_known(v___x_4289_, 1);
                    v___x_4371_ = l_Lean_Expr_isLet(v_a_4290_);
                    if v___x_4371_ == 0 {
                        v___x_4372_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clearValue___lam__0___closed__5),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_clearValue___lam__0___closed__5_once
                            ),
                            _init_l_Lean_MVarId_clearValue___lam__0___closed__5,
                        );
                        crate::leanh::lean_inc(v_fvarId_4281_);
                        v___x_4373_ = l_Lean_Expr_fvar___override(v_fvarId_4281_);
                        v___x_4374_ = l_Lean_MessageData_ofExpr(v___x_4373_);
                        v___x_4375_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4375_, 0, v___x_4372_);
                        crate::leanh::lean_ctor_set(v___x_4375_, 1, v___x_4374_);
                        v___x_4376_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clearValue___lam__0___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_clearValue___lam__0___closed__7_once
                            ),
                            _init_l_Lean_MVarId_clearValue___lam__0___closed__7,
                        );
                        v___x_4377_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4375_);
                        crate::leanh::lean_ctor_set(v___x_4377_, 1, v___x_4376_);
                        v___x_4378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4377_);
                        crate::leanh::lean_inc_n(v_mvarId_4283_, 2);
                        crate::leanh::lean_inc(v___x_4282_);
                        v___x_4379_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_throwTacticEx___boxed as *mut core::ffi::c_void,
                            9,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___x_4379_, 0, crate::leanh::lean_box(0));
                        crate::leanh::lean_closure_set(v___x_4379_, 1, v___x_4282_);
                        crate::leanh::lean_closure_set(v___x_4379_, 2, v_mvarId_4283_);
                        crate::leanh::lean_closure_set(v___x_4379_, 3, v___x_4378_);
                        v___x_4380_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(v_mvarId_4283_, v___x_4379_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
                        if crate::leanh::lean_obj_tag(v___x_4380_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4380_, 1);
                            v___y_4326_ = v___y_4284_;
                            v___y_4327_ = v___y_4285_;
                            v___y_4328_ = v___y_4286_;
                            v___y_4329_ = v___y_4287_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4290_);
                            crate::leanh::lean_dec(v_mvarId_4283_);
                            crate::leanh::lean_dec(v___x_4282_);
                            crate::leanh::lean_dec(v_fvarId_4281_);
                            crate::leanh::lean_dec_ref(v_fvars_4280_);
                            crate::leanh::lean_dec(v_a_4279_);
                            crate::leanh::lean_dec(v_mvarId_x27_4278_);
                            v_a_4381_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                            v_isSharedCheck_4388_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4380_)) as u8;
                            if v_isSharedCheck_4388_ == 0 {
                                v___x_4383_ = v___x_4380_;
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4381_);
                                crate::leanh::lean_dec(v___x_4380_);
                                v___x_4383_ = crate::leanh::lean_box(0);
                                v_isShared_4384_ = v_isSharedCheck_4388_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___y_4326_ = v___y_4284_;
                        v___y_4327_ = v___y_4285_;
                        v___y_4328_ = v___y_4286_;
                        v___y_4329_ = v___y_4287_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4283_);
                    crate::leanh::lean_dec(v___x_4282_);
                    crate::leanh::lean_dec(v_fvarId_4281_);
                    crate::leanh::lean_dec_ref(v_fvars_4280_);
                    crate::leanh::lean_dec(v_a_4279_);
                    crate::leanh::lean_dec(v_mvarId_x27_4278_);
                    v_a_4389_ = crate::leanh::lean_ctor_get(v___x_4289_, 0);
                    v_isSharedCheck_4396_ = (!crate::leanh::lean_is_exclusive(v___x_4289_)) as u8;
                    if v_isSharedCheck_4396_ == 0 {
                        v___x_4391_ = v___x_4289_;
                        v_isShared_4392_ = v_isSharedCheck_4396_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4389_);
                        crate::leanh::lean_dec(v___x_4289_);
                        v___x_4391_ = crate::leanh::lean_box(0);
                        v_isShared_4392_ = v_isSharedCheck_4396_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___y_4292_,
                    v_a_4279_,
                    v___y_4293_,
                    v___y_4294_,
                    v___y_4295_,
                    v___y_4296_,
                );
                if crate::leanh::lean_obj_tag(v___x_4297_) == 0 {
                    v_a_4298_ = crate::leanh::lean_ctor_get(v___x_4297_, 0);
                    crate::leanh::lean_inc_n(v_a_4298_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4297_, 1);
                    v___x_4299_ = l_Lean_Expr_letValue_x21(v_a_4290_);
                    crate::leanh::lean_dec(v_a_4290_);
                    v___x_4300_ = l_Lean_Expr_app___override(v_a_4298_, v___x_4299_);
                    v___x_4301_ =
                        l_Lean_MVarId_assign___at___00Lean_MVarId_replaceTargetEq_spec__0___redArg(
                            v_mvarId_x27_4278_,
                            v___x_4300_,
                            v___y_4294_,
                        );
                    v_isSharedCheck_4315_ = (!crate::leanh::lean_is_exclusive(v___x_4301_)) as u8;
                    if v_isSharedCheck_4315_ == 0 {
                        v_unused_4316_ = crate::leanh::lean_ctor_get(v___x_4301_, 0);
                        crate::leanh::lean_dec(v_unused_4316_);
                        v___x_4303_ = v___x_4301_;
                        v_isShared_4304_ = v_isSharedCheck_4315_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4301_);
                        v___x_4303_ = crate::leanh::lean_box(0);
                        v_isShared_4304_ = v_isSharedCheck_4315_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4290_);
                    crate::leanh::lean_dec_ref(v_fvars_4280_);
                    crate::leanh::lean_dec(v_mvarId_x27_4278_);
                    v_a_4317_ = crate::leanh::lean_ctor_get(v___x_4297_, 0);
                    v_isSharedCheck_4324_ = (!crate::leanh::lean_is_exclusive(v___x_4297_)) as u8;
                    if v_isSharedCheck_4324_ == 0 {
                        v___x_4319_ = v___x_4297_;
                        v_isShared_4320_ = v_isSharedCheck_4324_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4317_);
                        crate::leanh::lean_dec(v___x_4297_);
                        v___x_4319_ = crate::leanh::lean_box(0);
                        v_isShared_4320_ = v_isSharedCheck_4324_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4305_ = crate::leanh::lean_box(0);
                v_sz_4306_ = lean_array_size(v_fvars_4280_);
                v___x_4307_ = 0usize;
                v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_changeLocalDecl_spec__0(v_sz_4306_, v___x_4307_, v_fvars_4280_);
                v___x_4309_ = l_Lean_Expr_mvarId_x21(v_a_4298_);
                crate::leanh::lean_dec(v_a_4298_);
                v___x_4310_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4310_, 0, v___x_4308_);
                crate::leanh::lean_ctor_set(v___x_4310_, 1, v___x_4309_);
                v___x_4311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4311_, 0, v___x_4305_);
                crate::leanh::lean_ctor_set(v___x_4311_, 1, v___x_4310_);
                if v_isShared_4304_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4303_, 0, v___x_4311_);
                    v___x_4313_ = v___x_4303_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
                    v___x_4313_ = v_reuseFailAlloc_4314_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4313_;
            }
            4 => {
                if v_isShared_4320_ == 0 {
                    v___x_4322_ = v___x_4319_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
                    v___x_4322_ = v_reuseFailAlloc_4323_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4322_;
            }
            6 => {
                v___x_4330_ = l_Lean_Expr_letName_x21(v_a_4290_);
                v___x_4331_ = l_Lean_Expr_letType_x21(v_a_4290_);
                v___x_4332_ = l_Lean_Expr_letBody_x21(v_a_4290_);
                v___x_4333_ = 0;
                v___x_4334_ = l_Lean_Expr_forallE___override(
                    v___x_4330_,
                    v___x_4331_,
                    v___x_4332_,
                    v___x_4333_,
                );
                v___x_4335_ = l_Lean_instantiateMVars___at___00Lean_MVarId_replaceTargetDefEq_spec__0___redArg(v___x_4334_, v___y_4327_);
                v_a_4336_ = crate::leanh::lean_ctor_get(v___x_4335_, 0);
                v_isSharedCheck_4370_ = (!crate::leanh::lean_is_exclusive(v___x_4335_)) as u8;
                if v_isSharedCheck_4370_ == 0 {
                    v___x_4338_ = v___x_4335_;
                    v_isShared_4339_ = v_isSharedCheck_4370_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4336_);
                    crate::leanh::lean_dec(v___x_4335_);
                    v___x_4338_ = crate::leanh::lean_box(0);
                    v_isShared_4339_ = v_isSharedCheck_4370_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_a_4336_);
                v___x_4340_ = l_Lean_Meta_isTypeCorrect(
                    v_a_4336_,
                    v___y_4326_,
                    v___y_4327_,
                    v___y_4328_,
                    v___y_4329_,
                );
                if crate::leanh::lean_obj_tag(v___x_4340_) == 0 {
                    v_a_4341_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                    crate::leanh::lean_inc(v_a_4341_);
                    crate::leanh::lean_dec_ref_known(v___x_4340_, 1);
                    v___x_4342_ = (crate::leanh::lean_unbox(v_a_4341_) as u8);
                    crate::leanh::lean_dec(v_a_4341_);
                    if v___x_4342_ == 0 {
                        v___x_4343_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clearValue___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_clearValue___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_clearValue___lam__0___closed__1,
                        );
                        v___x_4344_ = l_Lean_Expr_fvar___override(v_fvarId_4281_);
                        v___x_4345_ = l_Lean_MessageData_ofExpr(v___x_4344_);
                        v___x_4346_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4346_, 0, v___x_4343_);
                        crate::leanh::lean_ctor_set(v___x_4346_, 1, v___x_4345_);
                        v___x_4347_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_clearValue___lam__0___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_clearValue___lam__0___closed__3_once
                            ),
                            _init_l_Lean_MVarId_clearValue___lam__0___closed__3,
                        );
                        v___x_4348_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4346_);
                        crate::leanh::lean_ctor_set(v___x_4348_, 1, v___x_4347_);
                        if v_isShared_4339_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4338_, 1);
                            crate::leanh::lean_ctor_set(v___x_4338_, 0, v___x_4348_);
                            v___x_4350_ = v___x_4338_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_4361_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4348_);
                            v___x_4350_ = v_reuseFailAlloc_4361_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4338_);
                        crate::leanh::lean_dec(v_mvarId_4283_);
                        crate::leanh::lean_dec(v___x_4282_);
                        crate::leanh::lean_dec(v_fvarId_4281_);
                        v___y_4292_ = v_a_4336_;
                        v___y_4293_ = v___y_4326_;
                        v___y_4294_ = v___y_4327_;
                        v___y_4295_ = v___y_4328_;
                        v___y_4296_ = v___y_4329_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4338_);
                    crate::leanh::lean_dec(v_a_4336_);
                    crate::leanh::lean_dec(v_a_4290_);
                    crate::leanh::lean_dec(v_mvarId_4283_);
                    crate::leanh::lean_dec(v___x_4282_);
                    crate::leanh::lean_dec(v_fvarId_4281_);
                    crate::leanh::lean_dec_ref(v_fvars_4280_);
                    crate::leanh::lean_dec(v_a_4279_);
                    crate::leanh::lean_dec(v_mvarId_x27_4278_);
                    v_a_4362_ = crate::leanh::lean_ctor_get(v___x_4340_, 0);
                    v_isSharedCheck_4369_ = (!crate::leanh::lean_is_exclusive(v___x_4340_)) as u8;
                    if v_isSharedCheck_4369_ == 0 {
                        v___x_4364_ = v___x_4340_;
                        v_isShared_4365_ = v_isSharedCheck_4369_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4362_);
                        crate::leanh::lean_dec(v___x_4340_);
                        v___x_4364_ = crate::leanh::lean_box(0);
                        v_isShared_4365_ = v_isSharedCheck_4369_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                crate::leanh::lean_inc(v_mvarId_4283_);
                v___x_4351_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_throwTacticEx___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_4351_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4351_, 1, v___x_4282_);
                crate::leanh::lean_closure_set(v___x_4351_, 2, v_mvarId_4283_);
                crate::leanh::lean_closure_set(v___x_4351_, 3, v___x_4350_);
                v___x_4352_ =
                    l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
                        v_mvarId_4283_,
                        v___x_4351_,
                        v___y_4326_,
                        v___y_4327_,
                        v___y_4328_,
                        v___y_4329_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4352_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4352_, 1);
                    v___y_4292_ = v_a_4336_;
                    v___y_4293_ = v___y_4326_;
                    v___y_4294_ = v___y_4327_;
                    v___y_4295_ = v___y_4328_;
                    v___y_4296_ = v___y_4329_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4336_);
                    crate::leanh::lean_dec(v_a_4290_);
                    crate::leanh::lean_dec_ref(v_fvars_4280_);
                    crate::leanh::lean_dec(v_a_4279_);
                    crate::leanh::lean_dec(v_mvarId_x27_4278_);
                    v_a_4353_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                    v_isSharedCheck_4360_ = (!crate::leanh::lean_is_exclusive(v___x_4352_)) as u8;
                    if v_isSharedCheck_4360_ == 0 {
                        v___x_4355_ = v___x_4352_;
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4353_);
                        crate::leanh::lean_dec(v___x_4352_);
                        v___x_4355_ = crate::leanh::lean_box(0);
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4356_ == 0 {
                    v___x_4358_ = v___x_4355_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
                    v___x_4358_ = v_reuseFailAlloc_4359_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4358_;
            }
            11 => {
                if v_isShared_4365_ == 0 {
                    v___x_4367_ = v___x_4364_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
                    v___x_4367_ = v_reuseFailAlloc_4368_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4367_;
            }
            13 => {
                if v_isShared_4384_ == 0 {
                    v___x_4386_ = v___x_4383_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4387_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4386_;
            }
            15 => {
                if v_isShared_4392_ == 0 {
                    v___x_4394_ = v___x_4391_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
                    v___x_4394_ = v_reuseFailAlloc_4395_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_clearValue___lam__0___boxed(
    mut v_mvarId_x27_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
    mut v_fvars_4399_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4400_: *mut crate::leanh::LeanObject,
    mut v___x_4401_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Lean_MVarId_clearValue___lam__0(
        v_mvarId_x27_4397_,
        v_a_4398_,
        v_fvars_4399_,
        v_fvarId_4400_,
        v___x_4401_,
        v_mvarId_4402_,
        v___y_4403_,
        v___y_4404_,
        v___y_4405_,
        v___y_4406_,
    );
    crate::leanh::lean_dec(v___y_4406_);
    crate::leanh::lean_dec_ref(v___y_4405_);
    crate::leanh::lean_dec(v___y_4404_);
    crate::leanh::lean_dec_ref(v___y_4403_);
    return v_res_4408_;
}
pub unsafe fn l_Lean_MVarId_clearValue___lam__1(
    mut v_a_4409_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4410_: *mut crate::leanh::LeanObject,
    mut v___x_4411_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4412_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_4413_: *mut crate::leanh::LeanObject,
    mut v_fvars_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
    mut v___y_4418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_x27_4413_);
    v___f_4420_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_clearValue___lam__0___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4420_, 0, v_mvarId_x27_4413_);
    crate::leanh::lean_closure_set(v___f_4420_, 1, v_a_4409_);
    crate::leanh::lean_closure_set(v___f_4420_, 2, v_fvars_4414_);
    crate::leanh::lean_closure_set(v___f_4420_, 3, v_fvarId_4410_);
    crate::leanh::lean_closure_set(v___f_4420_, 4, v___x_4411_);
    crate::leanh::lean_closure_set(v___f_4420_, 5, v_mvarId_4412_);
    v___x_4421_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_replaceTargetEq_spec__1___redArg(
        v_mvarId_x27_4413_,
        v___f_4420_,
        v___y_4415_,
        v___y_4416_,
        v___y_4417_,
        v___y_4418_,
    );
    return v___x_4421_;
}
pub unsafe fn l_Lean_MVarId_clearValue___lam__1___boxed(
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4423_: *mut crate::leanh::LeanObject,
    mut v___x_4424_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4425_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_4426_: *mut crate::leanh::LeanObject,
    mut v_fvars_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4433_ = l_Lean_MVarId_clearValue___lam__1(
        v_a_4422_,
        v_fvarId_4423_,
        v___x_4424_,
        v_mvarId_4425_,
        v_mvarId_x27_4426_,
        v_fvars_4427_,
        v___y_4428_,
        v___y_4429_,
        v___y_4430_,
        v___y_4431_,
    );
    crate::leanh::lean_dec(v___y_4431_);
    crate::leanh::lean_dec_ref(v___y_4430_);
    crate::leanh::lean_dec(v___y_4429_);
    crate::leanh::lean_dec_ref(v___y_4428_);
    return v_res_4433_;
}
pub unsafe fn l_Lean_MVarId_clearValue(
    mut v_mvarId_4437_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v_snd_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut v_a_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut v_a_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4478_: u8 = 0;
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4444_ = l_Lean_MVarId_clearValue___closed__1;
                crate::leanh::lean_inc(v_mvarId_4437_);
                v___x_4445_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4437_,
                    v___x_4444_,
                    v_a_4439_,
                    v_a_4440_,
                    v_a_4441_,
                    v_a_4442_,
                );
                if crate::leanh::lean_obj_tag(v___x_4445_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4445_, 1);
                    crate::leanh::lean_inc(v_mvarId_4437_);
                    v___x_4446_ = l_Lean_MVarId_getTag(
                        v_mvarId_4437_,
                        v_a_4439_,
                        v_a_4440_,
                        v_a_4441_,
                        v_a_4442_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4446_) == 0 {
                        v_a_4447_ = crate::leanh::lean_ctor_get(v___x_4446_, 0);
                        crate::leanh::lean_inc(v_a_4447_);
                        crate::leanh::lean_dec_ref_known(v___x_4446_, 1);
                        crate::leanh::lean_inc(v_mvarId_4437_);
                        crate::leanh::lean_inc(v_fvarId_4438_);
                        v___f_4448_ = crate::leanh::lean_alloc_closure(
                            l_Lean_MVarId_clearValue___lam__1___boxed as *mut core::ffi::c_void,
                            11,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_4448_, 0, v_a_4447_);
                        crate::leanh::lean_closure_set(v___f_4448_, 1, v_fvarId_4438_);
                        crate::leanh::lean_closure_set(v___f_4448_, 2, v___x_4444_);
                        crate::leanh::lean_closure_set(v___f_4448_, 3, v_mvarId_4437_);
                        v___x_4449_ = l_Lean_MVarId_withRevertedFrom___redArg(
                            v_mvarId_4437_,
                            v_fvarId_4438_,
                            v___f_4448_,
                            v_a_4439_,
                            v_a_4440_,
                            v_a_4441_,
                            v_a_4442_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4449_) == 0 {
                            v_a_4450_ = crate::leanh::lean_ctor_get(v___x_4449_, 0);
                            v_isSharedCheck_4458_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4449_)) as u8;
                            if v_isSharedCheck_4458_ == 0 {
                                v___x_4452_ = v___x_4449_;
                                v_isShared_4453_ = v_isSharedCheck_4458_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4450_);
                                crate::leanh::lean_dec(v___x_4449_);
                                v___x_4452_ = crate::leanh::lean_box(0);
                                v_isShared_4453_ = v_isSharedCheck_4458_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4449_, 0);
                            v_isSharedCheck_4466_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4449_)) as u8;
                            if v_isSharedCheck_4466_ == 0 {
                                v___x_4461_ = v___x_4449_;
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4459_);
                                crate::leanh::lean_dec(v___x_4449_);
                                v___x_4461_ = crate::leanh::lean_box(0);
                                v_isShared_4462_ = v_isSharedCheck_4466_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_4438_);
                        crate::leanh::lean_dec(v_mvarId_4437_);
                        v_a_4467_ = crate::leanh::lean_ctor_get(v___x_4446_, 0);
                        v_isSharedCheck_4474_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4446_)) as u8;
                        if v_isSharedCheck_4474_ == 0 {
                            v___x_4469_ = v___x_4446_;
                            v_isShared_4470_ = v_isSharedCheck_4474_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4467_);
                            crate::leanh::lean_dec(v___x_4446_);
                            v___x_4469_ = crate::leanh::lean_box(0);
                            v_isShared_4470_ = v_isSharedCheck_4474_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_4438_);
                    crate::leanh::lean_dec(v_mvarId_4437_);
                    v_a_4475_ = crate::leanh::lean_ctor_get(v___x_4445_, 0);
                    v_isSharedCheck_4482_ = (!crate::leanh::lean_is_exclusive(v___x_4445_)) as u8;
                    if v_isSharedCheck_4482_ == 0 {
                        v___x_4477_ = v___x_4445_;
                        v_isShared_4478_ = v_isSharedCheck_4482_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4475_);
                        crate::leanh::lean_dec(v___x_4445_);
                        v___x_4477_ = crate::leanh::lean_box(0);
                        v_isShared_4478_ = v_isSharedCheck_4482_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4454_ = crate::leanh::lean_ctor_get(v_a_4450_, 1);
                crate::leanh::lean_inc(v_snd_4454_);
                crate::leanh::lean_dec(v_a_4450_);
                if v_isShared_4453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4452_, 0, v_snd_4454_);
                    v___x_4456_ = v___x_4452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_snd_4454_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4456_;
            }
            3 => {
                if v_isShared_4462_ == 0 {
                    v___x_4464_ = v___x_4461_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4464_;
            }
            5 => {
                if v_isShared_4470_ == 0 {
                    v___x_4472_ = v___x_4469_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4472_;
            }
            7 => {
                if v_isShared_4478_ == 0 {
                    v___x_4480_ = v___x_4477_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
                    v___x_4480_ = v_reuseFailAlloc_4481_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_clearValue___boxed(
    mut v_mvarId_4483_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_a_4486_: *mut crate::leanh::LeanObject,
    mut v_a_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lean_MVarId_clearValue(
        v_mvarId_4483_,
        v_fvarId_4484_,
        v_a_4485_,
        v_a_4486_,
        v_a_4487_,
        v_a_4488_,
    );
    crate::leanh::lean_dec(v_a_4488_);
    crate::leanh::lean_dec_ref(v_a_4487_);
    crate::leanh::lean_dec(v_a_4486_);
    crate::leanh::lean_dec_ref(v_a_4485_);
    return v_res_4490_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Replace(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Replace(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Replace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_InfoTree_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Replace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Replace(builtin);
}
