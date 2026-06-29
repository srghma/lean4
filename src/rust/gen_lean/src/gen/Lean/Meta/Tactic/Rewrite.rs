// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.KAbstract Lean.Meta.Tactic.Apply Lean.Meta.BinderNameHint
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_const___override,
    l_Lean_Expr_getAppFn, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkApp6, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkLambda,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_inlineExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqSymm,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::BinderNameHint::{
    initialize_Lean_Meta_BinderNameHint, l_Lean_Expr_hasBinderNameHint,
    l_Lean_Expr_resolveBinderNameHint, runtime_initialize_Lean_Meta_BinderNameHint,
};
use crate::r#gen::Lean::Meta::Check::{l_Lean_Meta_addPPExplicitToExposeDiff, l_Lean_Meta_check};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVarsNoDelayed;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::KAbstract::{
    initialize_Lean_Meta_KAbstract, l_Lean_Meta_kabstract, runtime_initialize_Lean_Meta_KAbstract,
};
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchEq_x3f, runtime_initialize_Lean_Meta_MatchUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_Meta_appendParentTag,
    l_Lean_Meta_postprocessAppMVars, runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_Meta_tactic_skipAssignedInstances,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_expr_instantiate1;
use crate::ffi::lean_infer_type;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1: usize = 0;
pub static l_Lean_MVarId_rewrite___lam__1___closed__0_value: crate::leanh::LeanStringObject<84> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 84,
        m_capacity: 84,
        m_length: 83,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 114, 101, 119, 114, 105, 116, 101, 32, 97, 114,
            103, 117, 109, 101, 110, 116, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 97,
            110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 114, 32, 105, 102, 102, 32,
            112, 114, 111, 111, 102, 32, 111, 114, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111,
            110, 32, 110, 97, 109, 101, 44, 32, 98, 117, 116, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 115, 32, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__4_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__5_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__5_value)
                as *mut crate::leanh::LeanObject,
            2642306550782628284 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__7_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            77, 111, 116, 105, 118, 101, 32, 105, 115, 32, 100, 101, 112, 101, 110, 100, 101, 110,
            116, 58, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__9_value: crate::leanh::LeanStringObject<122> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 122,
        m_capacity: 122,
        m_length: 121,
        m_data: [
            84, 104, 101, 32, 114, 101, 119, 114, 105, 116, 101, 32, 116, 97, 99, 116, 105, 99, 32,
            99, 97, 110, 110, 111, 116, 32, 115, 117, 98, 115, 116, 105, 116, 117, 116, 101, 32,
            116, 101, 114, 109, 115, 32, 111, 110, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101,
            32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101,
            116, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 100, 101, 112, 101, 110,
            100, 115, 46, 32, 84, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104,
            101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__11_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            10, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 116, 104, 101, 32, 118, 97,
            108, 117, 101, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__13_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
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
            109, 111, 116, 105, 118, 101, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101,
            32, 99, 111, 114, 114, 101, 99, 116, 58, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__15_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [10, 69, 114, 114, 111, 114, 58, 32, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__17_value: crate::leanh::LeanStringObject<353> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 353,
        m_capacity: 353,
        m_length: 352,
        m_data: [
            10, 10, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 58, 32, 84, 104, 101, 32,
            114, 101, 119, 114, 105, 116, 101, 32, 116, 97, 99, 116, 105, 99, 32, 114, 101, 119,
            114, 105, 116, 101, 115, 32, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111,
            110, 32, 39, 101, 39, 32, 117, 115, 105, 110, 103, 32, 97, 110, 32, 101, 113, 117, 97,
            108, 105, 116, 121, 32, 39, 97, 32, 61, 32, 98, 39, 32, 98, 121, 32, 116, 104, 101, 32,
            102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 112, 114, 111, 99, 101, 115, 115, 46,
            32, 70, 105, 114, 115, 116, 44, 32, 105, 116, 32, 108, 111, 111, 107, 115, 32, 102,
            111, 114, 32, 97, 108, 108, 32, 39, 97, 39, 32, 105, 110, 32, 39, 101, 39, 46, 32, 83,
            101, 99, 111, 110, 100, 44, 32, 105, 116, 32, 116, 114, 105, 101, 115, 32, 116, 111,
            32, 97, 98, 115, 116, 114, 97, 99, 116, 32, 116, 104, 101, 115, 101, 32, 111, 99, 99,
            117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 39, 97, 39, 32, 116, 111, 32,
            99, 114, 101, 97, 116, 101, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 39,
            109, 32, 58, 61, 32, 102, 117, 110, 32, 95, 97, 32, 61, 62, 32, 46, 46, 46, 39, 44, 32,
            99, 97, 108, 108, 101, 100, 32, 116, 104, 101, 32, 42, 109, 111, 116, 105, 118, 101,
            42, 44, 32, 119, 105, 116, 104, 32, 116, 104, 101, 32, 112, 114, 111, 112, 101, 114,
            116, 121, 32, 116, 104, 97, 116, 32, 39, 109, 32, 97, 39, 32, 105, 115, 32, 100, 101,
            102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108,
            32, 116, 111, 32, 39, 101, 39, 46, 32, 84, 104, 105, 114, 100, 44, 32, 119, 101, 32,
            111, 98, 115, 101, 114, 118, 101, 32, 116, 104, 97, 116, 32, 39, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__19_value: crate::leanh::LeanStringObject<68> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            39, 32, 105, 109, 112, 108, 105, 101, 115, 32, 116, 104, 97, 116, 32, 39, 109, 32, 97,
            32, 61, 32, 109, 32, 98, 39, 44, 32, 119, 104, 105, 99, 104, 32, 99, 97, 110, 32, 98,
            101, 32, 117, 115, 101, 100, 32, 119, 105, 116, 104, 32, 108, 101, 109, 109, 97, 115,
            32, 115, 117, 99, 104, 32, 97, 115, 32, 39, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__21_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_MVarId_rewrite___lam__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__22_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_MVarId_rewrite___lam__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__21_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_rewrite___lam__1___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__23_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__22_value)
                as *mut crate::leanh::LeanObject,
            503120329516084626 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__24_value: crate::leanh::LeanStringObject<348> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 348,
        m_capacity: 348,
        m_length: 347,
        m_data: [
            39, 32, 116, 111, 32, 99, 104, 97, 110, 103, 101, 32, 116, 104, 101, 32, 103, 111, 97,
            108, 46, 32, 72, 111, 119, 101, 118, 101, 114, 44, 32, 105, 102, 32, 39, 101, 39, 32,
            100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 115, 112, 101, 99, 105, 102, 105,
            99, 32, 112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 32, 111, 102, 32, 39, 97, 39,
            44, 32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 109, 111, 116, 105, 118, 101, 32,
            39, 109, 39, 32, 109, 105, 103, 104, 116, 32, 110, 111, 116, 32, 116, 121, 112, 101,
            99, 104, 101, 99, 107, 46, 10, 10, 80, 111, 115, 115, 105, 98, 108, 101, 32, 115, 111,
            108, 117, 116, 105, 111, 110, 115, 58, 32, 117, 115, 101, 32, 114, 101, 119, 114, 105,
            116, 101, 39, 115, 32, 39, 111, 99, 99, 115, 39, 32, 99, 111, 110, 102, 105, 103, 117,
            114, 97, 116, 105, 111, 110, 32, 111, 112, 116, 105, 111, 110, 32, 116, 111, 32, 108,
            105, 109, 105, 116, 32, 119, 104, 105, 99, 104, 32, 111, 99, 99, 117, 114, 114, 101,
            110, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 119, 114, 105, 116, 116, 101, 110,
            44, 32, 111, 114, 32, 117, 115, 101, 32, 39, 115, 105, 109, 112, 39, 32, 111, 114, 32,
            39, 99, 111, 110, 118, 39, 32, 109, 111, 100, 101, 44, 32, 119, 104, 105, 99, 104, 32,
            104, 97, 118, 101, 32, 115, 116, 114, 97, 116, 101, 103, 105, 101, 115, 32, 102, 111,
            114, 32, 99, 101, 114, 116, 97, 105, 110, 32, 107, 105, 110, 100, 115, 32, 111, 102,
            32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 32, 40, 116, 104, 101,
            115, 101, 32, 116, 97, 99, 116, 105, 99, 115, 32, 99, 97, 110, 32, 104, 97, 110, 100,
            108, 101, 32, 112, 114, 111, 111, 102, 115, 32, 97, 110, 100, 32, 39, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__24_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__26_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__27_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__26_value)
                as *mut crate::leanh::LeanObject,
            4342836574150310743 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__28_value: crate::leanh::LeanStringObject<118> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 118,
        m_capacity: 118,
        m_length: 117,
        m_data: [
            39, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 119, 104, 111, 115, 101, 32,
            116, 121, 112, 101, 115, 32, 100, 101, 112, 101, 110, 100, 32, 111, 110, 32, 116, 104,
            101, 32, 114, 101, 119, 114, 105, 116, 116, 101, 110, 32, 116, 101, 114, 109, 44, 32,
            97, 110, 100, 32, 39, 115, 105, 109, 112, 39, 32, 99, 97, 110, 32, 97, 112, 112, 108,
            121, 32, 117, 115, 101, 114, 45, 100, 101, 102, 105, 110, 101, 100, 32, 39, 64, 91, 99,
            111, 110, 103, 114, 93, 39, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 97, 115,
            32, 119, 101, 108, 108, 41, 46, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__30_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [95, 97, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__31_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__30_value)
                as *mut crate::leanh::LeanObject,
            12238201060643072740 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__32_value: crate::leanh::LeanStringObject<42> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            68, 105, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 32, 111, 99, 99,
            117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 116, 104, 101, 32, 112, 97, 116,
            116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__32_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__34_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            10, 105, 110, 32, 116, 104, 101, 32, 116, 97, 114, 103, 101, 116, 32, 101, 120, 112,
            114, 101, 115, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__34_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__35_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__36_value: crate::leanh::LeanStringObject<77> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 77,
        m_capacity: 77,
        m_length: 76,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 114, 101, 119, 114, 105, 116, 101, 32, 97, 114,
            103, 117, 109, 101, 110, 116, 58, 32, 84, 104, 101, 32, 112, 97, 116, 116, 101, 114,
            110, 32, 116, 111, 32, 98, 101, 32, 115, 117, 98, 115, 116, 105, 116, 117, 116, 101,
            100, 32, 105, 115, 32, 97, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101,
            32, 40, 96, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__36_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__38_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            96, 41, 32, 105, 110, 32, 116, 104, 105, 115, 32, 101, 113, 117, 97, 108, 105, 116,
            121, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__38_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__39_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___lam__1___closed__40_value: crate::leanh::LeanStringObject<16> =
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
            97, 32, 118, 97, 108, 117, 101, 32, 111, 102, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__41_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [97, 32, 112, 114, 111, 111, 102, 32, 111, 102, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__42_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [73, 102, 102, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__43_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__42_value)
                as *mut crate::leanh::LeanObject,
            9917798623386220051 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__44_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 114, 111, 112, 101, 120, 116, 0],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___lam__1___closed__45_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__44_value)
                as *mut crate::leanh::LeanObject,
            12404887534527682101 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___lam__1___closed__45_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_rewrite___lam__1___closed__46_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_rewrite___lam__1___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_rewrite___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [114, 101, 119, 114, 105, 116, 101, 0],
    };
static mut l_Lean_MVarId_rewrite___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_rewrite___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_rewrite___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12013589835852235629 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_rewrite___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_rewrite___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
    mut v_e_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1278_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_unused_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = l_Lean_Expr_hasMVar(v_e_1261_);
                if v___x_1264_ == 0 {
                    v___x_1265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1265_, 0, v_e_1261_);
                    return v___x_1265_;
                } else {
                    v___x_1266_ = lean_st_ref_get(v___y_1262_);
                    v_mctx_1267_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1267_);
                    crate::leanh::lean_dec(v___x_1266_);
                    v___x_1268_ = l_Lean_instantiateMVarsCore(v_mctx_1267_, v_e_1261_);
                    v_fst_1269_ = crate::leanh::lean_ctor_get(v___x_1268_, 0);
                    crate::leanh::lean_inc(v_fst_1269_);
                    v_snd_1270_ = crate::leanh::lean_ctor_get(v___x_1268_, 1);
                    crate::leanh::lean_inc(v_snd_1270_);
                    crate::leanh::lean_dec_ref(v___x_1268_);
                    v___x_1271_ = lean_st_ref_take(v___y_1262_);
                    v_cache_1272_ = crate::leanh::lean_ctor_get(v___x_1271_, 1);
                    v_zetaDeltaFVarIds_1273_ = crate::leanh::lean_ctor_get(v___x_1271_, 2);
                    v_postponed_1274_ = crate::leanh::lean_ctor_get(v___x_1271_, 3);
                    v_diag_1275_ = crate::leanh::lean_ctor_get(v___x_1271_, 4);
                    v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v___x_1271_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v_unused_1285_ = crate::leanh::lean_ctor_get(v___x_1271_, 0);
                        crate::leanh::lean_dec(v_unused_1285_);
                        v___x_1277_ = v___x_1271_;
                        v_isShared_1278_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1275_);
                        crate::leanh::lean_inc(v_postponed_1274_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1273_);
                        crate::leanh::lean_inc(v_cache_1272_);
                        crate::leanh::lean_dec(v___x_1271_);
                        v___x_1277_ = crate::leanh::lean_box(0);
                        v_isShared_1278_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v_snd_1270_);
                    v___x_1280_ = v___x_1277_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_snd_1270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_cache_1272_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1283_,
                        2,
                        v_zetaDeltaFVarIds_1273_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_postponed_1274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 4, v_diag_1275_);
                    v___x_1280_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1281_ = lean_st_ref_set(v___y_1262_, v___x_1280_);
                v___x_1282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1282_, 0, v_fst_1269_);
                return v___x_1282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg___boxed(
    mut v_e_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
        v_e_1286_,
        v___y_1287_,
    );
    crate::leanh::lean_dec(v___y_1287_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(
    mut v_e_1290_: *mut crate::leanh::LeanObject,
    mut v___y_1291_: *mut crate::leanh::LeanObject,
    mut v___y_1292_: *mut crate::leanh::LeanObject,
    mut v___y_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1296_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
        v_e_1290_,
        v___y_1292_,
    );
    return v___x_1296_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___boxed(
    mut v_e_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
    mut v___y_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1(
        v_e_1297_,
        v___y_1298_,
        v___y_1299_,
        v___y_1300_,
        v___y_1301_,
    );
    crate::leanh::lean_dec(v___y_1301_);
    crate::leanh::lean_dec_ref(v___y_1300_);
    crate::leanh::lean_dec(v___y_1299_);
    crate::leanh::lean_dec_ref(v___y_1298_);
    return v_res_1303_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(
    mut v_opts_1304_: *mut crate::leanh::LeanObject,
    mut v_opt_1305_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1306_ = crate::leanh::lean_ctor_get(v_opt_1305_, 0);
    v_defValue_1307_ = crate::leanh::lean_ctor_get(v_opt_1305_, 1);
    v_map_1308_ = crate::leanh::lean_ctor_get(v_opts_1304_, 0);
    v___x_1309_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1308_,
            v_name_1306_,
        );
    if crate::leanh::lean_obj_tag(v___x_1309_) == 0 {
        let mut v___x_1310_: u8 = 0;
        v___x_1310_ = (crate::leanh::lean_unbox(v_defValue_1307_) as u8);
        return v___x_1310_;
    } else {
        let mut v_val_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1311_ = crate::leanh::lean_ctor_get(v___x_1309_, 0);
        crate::leanh::lean_inc(v_val_1311_);
        crate::leanh::lean_dec_ref_known(v___x_1309_, 1);
        if crate::leanh::lean_obj_tag(v_val_1311_) == 1 {
            let mut v_v_1312_: u8 = 0;
            v_v_1312_ = crate::leanh::lean_ctor_get_uint8(v_val_1311_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1311_, 0);
            return v_v_1312_;
        } else {
            let mut v___x_1313_: u8 = 0;
            crate::leanh::lean_dec(v_val_1311_);
            v___x_1313_ = (crate::leanh::lean_unbox(v_defValue_1307_) as u8);
            return v___x_1313_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7___boxed(
    mut v_opts_1314_: *mut crate::leanh::LeanObject,
    mut v_opt_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1316_: u8 = 0;
    let mut v_r_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(v_opts_1314_, v_opt_1315_);
    crate::leanh::lean_dec_ref(v_opt_1315_);
    crate::leanh::lean_dec_ref(v_opts_1314_);
    v_r_1317_ = crate::leanh::lean_box((v_res_1316_) as usize);
    return v_r_1317_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(
    mut v_mvarId_1318_: *mut crate::leanh::LeanObject,
    mut v_x_1319_: *mut crate::leanh::LeanObject,
    mut v___y_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1325_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1318_,
                    v_x_1319_,
                    v___y_1320_,
                    v___y_1321_,
                    v___y_1322_,
                    v___y_1323_,
                );
                if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1333_ = (!crate::leanh::lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1333_ == 0 {
                        v___x_1328_ = v___x_1325_;
                        v_isShared_1329_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1326_);
                        crate::leanh::lean_dec(v___x_1325_);
                        v___x_1328_ = crate::leanh::lean_box(0);
                        v_isShared_1329_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1341_ = (!crate::leanh::lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1336_ = v___x_1325_;
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1334_);
                        crate::leanh::lean_dec(v___x_1325_);
                        v___x_1336_ = crate::leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1341_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1329_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
                    v___x_1331_ = v_reuseFailAlloc_1332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1331_;
            }
            3 => {
                if v_isShared_1337_ == 0 {
                    v___x_1339_ = v___x_1336_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg___boxed(
    mut v_mvarId_1342_: *mut crate::leanh::LeanObject,
    mut v_x_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(
        v_mvarId_1342_,
        v_x_1343_,
        v___y_1344_,
        v___y_1345_,
        v___y_1346_,
        v___y_1347_,
    );
    crate::leanh::lean_dec(v___y_1347_);
    crate::leanh::lean_dec_ref(v___y_1346_);
    crate::leanh::lean_dec(v___y_1345_);
    crate::leanh::lean_dec_ref(v___y_1344_);
    return v_res_1349_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(
    mut v_00_u03b1_1350_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1351_: *mut crate::leanh::LeanObject,
    mut v_x_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
    mut v___y_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(
        v_mvarId_1351_,
        v_x_1352_,
        v___y_1353_,
        v___y_1354_,
        v___y_1355_,
        v___y_1356_,
    );
    return v___x_1358_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___boxed(
    mut v_00_u03b1_1359_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9(
        v_00_u03b1_1359_,
        v_mvarId_1360_,
        v_x_1361_,
        v___y_1362_,
        v___y_1363_,
        v___y_1364_,
        v___y_1365_,
    );
    crate::leanh::lean_dec(v___y_1365_);
    crate::leanh::lean_dec_ref(v___y_1364_);
    crate::leanh::lean_dec(v___y_1363_);
    crate::leanh::lean_dec_ref(v___y_1362_);
    return v_res_1367_;
}
pub unsafe fn l_Lean_MVarId_rewrite___lam__0(
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1376_ = lean_expr_instantiate1(v_a_1368_, v_a_1370_);
                crate::leanh::lean_inc(v___y_1374_);
                crate::leanh::lean_inc_ref(v___y_1373_);
                crate::leanh::lean_inc(v___y_1372_);
                crate::leanh::lean_inc_ref(v___y_1371_);
                v___x_1377_ = lean_infer_type(
                    v___x_1376_,
                    v___y_1371_,
                    v___y_1372_,
                    v___y_1373_,
                    v___y_1374_,
                );
                if crate::leanh::lean_obj_tag(v___x_1377_) == 0 {
                    v_a_1378_ = crate::leanh::lean_ctor_get(v___x_1377_, 0);
                    crate::leanh::lean_inc(v_a_1378_);
                    crate::leanh::lean_dec_ref_known(v___x_1377_, 1);
                    v___x_1379_ = l_Lean_Meta_isExprDefEq(
                        v_a_1378_,
                        v_a_1369_,
                        v___y_1371_,
                        v___y_1372_,
                        v___y_1373_,
                        v___y_1374_,
                    );
                    return v___x_1379_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_1369_);
                    v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1377_, 0);
                    v_isSharedCheck_1387_ = (!crate::leanh::lean_is_exclusive(v___x_1377_)) as u8;
                    if v_isSharedCheck_1387_ == 0 {
                        v___x_1382_ = v___x_1377_;
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1380_);
                        crate::leanh::lean_dec(v___x_1377_);
                        v___x_1382_ = crate::leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1383_ == 0 {
                    v___x_1385_ = v___x_1382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_rewrite___lam__0___boxed(
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_MVarId_rewrite___lam__0(
        v_a_1388_,
        v_a_1389_,
        v_a_1390_,
        v___y_1391_,
        v___y_1392_,
        v___y_1393_,
        v___y_1394_,
    );
    crate::leanh::lean_dec(v___y_1394_);
    crate::leanh::lean_dec_ref(v___y_1393_);
    crate::leanh::lean_dec(v___y_1392_);
    crate::leanh::lean_dec_ref(v___y_1391_);
    crate::leanh::lean_dec_ref(v_a_1390_);
    crate::leanh::lean_dec_ref(v_a_1388_);
    return v_res_1396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(
    mut v_sz_1397_: usize,
    mut v_i_1398_: usize,
    mut v_bs_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: u8 = 0;
    let mut v_v_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: usize = 0;
    let mut v___x_1406_: usize = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = lean_usize_dec_lt(v_i_1398_, v_sz_1397_);
                if v___x_1400_ == 0 {
                    return v_bs_1399_;
                } else {
                    v_v_1401_ = lean_array_uget(v_bs_1399_, v_i_1398_);
                    v___x_1402_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1403_ = lean_array_uset(v_bs_1399_, v_i_1398_, v___x_1402_);
                    v___x_1404_ = l_Lean_Expr_mvarId_x21(v_v_1401_);
                    crate::leanh::lean_dec(v_v_1401_);
                    v___x_1405_ = 1usize;
                    v___x_1406_ = lean_usize_add(v_i_1398_, v___x_1405_);
                    v___x_1407_ = lean_array_uset(v_bs_x27_1403_, v_i_1398_, v___x_1404_);
                    v_i_1398_ = v___x_1406_;
                    v_bs_1399_ = v___x_1407_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3___boxed(
    mut v_sz_1409_: *mut crate::leanh::LeanObject,
    mut v_i_1410_: *mut crate::leanh::LeanObject,
    mut v_bs_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1412_: usize = 0;
    let mut v_i_boxed_1413_: usize = 0;
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1412_ = crate::leanh::lean_unbox_usize(v_sz_1409_);
    crate::leanh::lean_dec(v_sz_1409_);
    v_i_boxed_1413_ = crate::leanh::lean_unbox_usize(v_i_1410_);
    crate::leanh::lean_dec(v_i_1410_);
    v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_boxed_1412_, v_i_boxed_1413_, v_bs_1411_);
    return v_res_1414_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(
    mut v_keys_1415_: *mut crate::leanh::LeanObject,
    mut v_i_1416_: *mut crate::leanh::LeanObject,
    mut v_k_1417_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v_k_x27_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1418_ = lean_array_get_size(v_keys_1415_);
                v___x_1419_ = lean_nat_dec_lt(v_i_1416_, v___x_1418_);
                if v___x_1419_ == 0 {
                    crate::leanh::lean_dec(v_i_1416_);
                    return v___x_1419_;
                } else {
                    v_k_x27_1420_ = lean_array_fget_borrowed(v_keys_1415_, v_i_1416_);
                    v___x_1421_ = l_Lean_instBEqMVarId_beq(v_k_1417_, v_k_x27_1420_);
                    if v___x_1421_ == 0 {
                        v___x_1422_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1423_ = lean_nat_add(v_i_1416_, v___x_1422_);
                        crate::leanh::lean_dec(v_i_1416_);
                        v_i_1416_ = v___x_1423_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1416_);
                        return v___x_1421_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg___boxed(
    mut v_keys_1425_: *mut crate::leanh::LeanObject,
    mut v_i_1426_: *mut crate::leanh::LeanObject,
    mut v_k_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1428_: u8 = 0;
    let mut v_r_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_1425_, v_i_1426_, v_k_1427_);
    crate::leanh::lean_dec(v_k_1427_);
    crate::leanh::lean_dec_ref(v_keys_1425_);
    v_r_1429_ = crate::leanh::lean_box((v_res_1428_) as usize);
    return v_r_1429_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1430_: usize = 0;
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: usize = 0;
    v___x_1430_ = 5usize;
    v___x_1431_ = 1usize;
    v___x_1432_ = lean_usize_shift_left(v___x_1431_, v___x_1430_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1433_: usize = 0;
    let mut v___x_1434_: usize = 0;
    let mut v___x_1435_: usize = 0;
    v___x_1433_ = 1usize;
    v___x_1434_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__0);
    v___x_1435_ = lean_usize_sub(v___x_1434_, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(
    mut v_x_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: usize,
    mut v_x_1438_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: usize = 0;
    let mut v___x_1442_: usize = 0;
    let mut v___x_1443_: usize = 0;
    let mut v_j_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v_node_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: usize = 0;
    let mut v___x_1451_: u8 = 0;
    let mut v_ks_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1436_) == 0 {
                    v_es_1439_ = crate::leanh::lean_ctor_get(v_x_1436_, 0);
                    v___x_1440_ = crate::leanh::lean_box(2);
                    v___x_1441_ = 5usize;
                    v___x_1442_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___closed__1);
                    v___x_1443_ = lean_usize_land(v_x_1437_, v___x_1442_);
                    v_j_1444_ = lean_usize_to_nat(v___x_1443_);
                    v___x_1445_ = lean_array_get_borrowed(v___x_1440_, v_es_1439_, v_j_1444_);
                    crate::leanh::lean_dec(v_j_1444_);
                    match crate::leanh::lean_obj_tag(v___x_1445_) {
                        0 => {
                            v_key_1446_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                            v___x_1447_ = l_Lean_instBEqMVarId_beq(v_x_1438_, v_key_1446_);
                            return v___x_1447_;
                        }
                        1 => {
                            v_node_1448_ = crate::leanh::lean_ctor_get(v___x_1445_, 0);
                            v___x_1449_ = lean_usize_shift_right(v_x_1437_, v___x_1441_);
                            v_x_1436_ = v_node_1448_;
                            v_x_1437_ = v___x_1449_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1451_ = 0;
                            return v___x_1451_;
                        }
                    }
                } else {
                    v_ks_1452_ = crate::leanh::lean_ctor_get(v_x_1436_, 0);
                    v___x_1453_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1454_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_ks_1452_, v___x_1453_, v_x_1438_);
                    return v___x_1454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18352__boxed_1458_: usize = 0;
    let mut v_res_1459_: u8 = 0;
    let mut v_r_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18352__boxed_1458_ = crate::leanh::lean_unbox_usize(v_x_1456_);
    crate::leanh::lean_dec(v_x_1456_);
    v_res_1459_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1455_, v_x_18352__boxed_1458_, v_x_1457_);
    crate::leanh::lean_dec(v_x_1457_);
    crate::leanh::lean_dec_ref(v_x_1455_);
    v_r_1460_ = crate::leanh::lean_box((v_res_1459_) as usize);
    return v_r_1460_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(
    mut v_x_1461_: *mut crate::leanh::LeanObject,
    mut v_x_1462_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1463_: u64 = 0;
    let mut v___x_1464_: usize = 0;
    let mut v___x_1465_: u8 = 0;
    v___x_1463_ = l_Lean_instHashableMVarId_hash(v_x_1462_);
    v___x_1464_ = lean_uint64_to_usize(v___x_1463_);
    v___x_1465_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_1461_, v___x_1464_, v_x_1462_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg___boxed(
    mut v_x_1466_: *mut crate::leanh::LeanObject,
    mut v_x_1467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1468_: u8 = 0;
    let mut v_r_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1468_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_1466_, v_x_1467_);
    crate::leanh::lean_dec(v_x_1467_);
    crate::leanh::lean_dec_ref(v_x_1466_);
    v_r_1469_ = crate::leanh::lean_box((v_res_1468_) as usize);
    return v_r_1469_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(
    mut v_mvarId_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = lean_st_ref_get(v___y_1471_);
    v_mctx_1474_ = crate::leanh::lean_ctor_get(v___x_1473_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1474_);
    crate::leanh::lean_dec(v___x_1473_);
    v_eAssignment_1475_ = crate::leanh::lean_ctor_get(v_mctx_1474_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_1475_);
    crate::leanh::lean_dec_ref(v_mctx_1474_);
    v___x_1476_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_eAssignment_1475_, v_mvarId_1470_);
    crate::leanh::lean_dec_ref(v_eAssignment_1475_);
    v___x_1477_ = crate::leanh::lean_box((v___x_1476_) as usize);
    v___x_1478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg___boxed(
    mut v_mvarId_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(
        v_mvarId_1479_,
        v___y_1480_,
    );
    crate::leanh::lean_dec(v___y_1480_);
    crate::leanh::lean_dec(v_mvarId_1479_);
    return v_res_1482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(
    mut v_as_1483_: *mut crate::leanh::LeanObject,
    mut v_i_1484_: usize,
    mut v_stop_1485_: usize,
    mut v_b_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
    mut v___y_1488_: *mut crate::leanh::LeanObject,
    mut v___y_1489_: *mut crate::leanh::LeanObject,
    mut v___y_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: usize = 0;
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u8 = 0;
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v_a_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1509_: u8 = 0;
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1497_ = lean_usize_dec_eq(v_i_1484_, v_stop_1485_);
                if v___x_1497_ == 0 {
                    v___x_1498_ = lean_array_uget_borrowed(v_as_1483_, v_i_1484_);
                    v___x_1501_ =
                        l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(
                            v___x_1498_,
                            v___y_1488_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1501_) == 0 {
                        v_a_1502_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                        crate::leanh::lean_inc(v_a_1502_);
                        crate::leanh::lean_dec_ref_known(v___x_1501_, 1);
                        v___x_1503_ = (crate::leanh::lean_unbox(v_a_1502_) as u8);
                        crate::leanh::lean_dec(v_a_1502_);
                        if v___x_1503_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1493_ = v_b_1486_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1501_) == 0 {
                            v_a_1504_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                            crate::leanh::lean_inc(v_a_1504_);
                            crate::leanh::lean_dec_ref_known(v___x_1501_, 1);
                            v___x_1505_ = (crate::leanh::lean_unbox(v_a_1504_) as u8);
                            crate::leanh::lean_dec(v_a_1504_);
                            if v___x_1505_ == 0 {
                                v_a_1493_ = v_b_1486_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_1486_);
                            v_a_1506_ = crate::leanh::lean_ctor_get(v___x_1501_, 0);
                            v_isSharedCheck_1513_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1501_)) as u8;
                            if v_isSharedCheck_1513_ == 0 {
                                v___x_1508_ = v___x_1501_;
                                v_isShared_1509_ = v_isSharedCheck_1513_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1506_);
                                crate::leanh::lean_dec(v___x_1501_);
                                v___x_1508_ = crate::leanh::lean_box(0);
                                v_isShared_1509_ = v_isSharedCheck_1513_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1514_, 0, v_b_1486_);
                    return v___x_1514_;
                }
            }
            1 => {
                v___x_1494_ = 1usize;
                v___x_1495_ = lean_usize_add(v_i_1484_, v___x_1494_);
                v_i_1484_ = v___x_1495_;
                v_b_1486_ = v_a_1493_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_1498_);
                v___x_1500_ = lean_array_push(v_b_1486_, v___x_1498_);
                v_a_1493_ = v___x_1500_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_1509_ == 0 {
                    v___x_1511_ = v___x_1508_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
                    v___x_1511_ = v_reuseFailAlloc_1512_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6___boxed(
    mut v_as_1515_: *mut crate::leanh::LeanObject,
    mut v_i_1516_: *mut crate::leanh::LeanObject,
    mut v_stop_1517_: *mut crate::leanh::LeanObject,
    mut v_b_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1524_: usize = 0;
    let mut v_stop_boxed_1525_: usize = 0;
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1524_ = crate::leanh::lean_unbox_usize(v_i_1516_);
    crate::leanh::lean_dec(v_i_1516_);
    v_stop_boxed_1525_ = crate::leanh::lean_unbox_usize(v_stop_1517_);
    crate::leanh::lean_dec(v_stop_1517_);
    v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v_as_1515_, v_i_boxed_1524_, v_stop_boxed_1525_, v_b_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    crate::leanh::lean_dec(v___y_1520_);
    crate::leanh::lean_dec_ref(v___y_1519_);
    crate::leanh::lean_dec_ref(v_as_1515_);
    return v_res_1526_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(
    mut v_k_1527_: *mut crate::leanh::LeanObject,
    mut v_b_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1532_);
    crate::leanh::lean_inc_ref(v___y_1531_);
    crate::leanh::lean_inc(v___y_1530_);
    crate::leanh::lean_inc_ref(v___y_1529_);
    v___x_1534_ = crate::leanh::lean_apply_6(
        v_k_1527_,
        v_b_1528_,
        v___y_1529_,
        v___y_1530_,
        v___y_1531_,
        v___y_1532_,
        crate::leanh::lean_box(0),
    );
    return v___x_1534_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed(
    mut v_k_1535_: *mut crate::leanh::LeanObject,
    mut v_b_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0(v_k_1535_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
    crate::leanh::lean_dec(v___y_1540_);
    crate::leanh::lean_dec_ref(v___y_1539_);
    crate::leanh::lean_dec(v___y_1538_);
    crate::leanh::lean_dec_ref(v___y_1537_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(
    mut v_name_1543_: *mut crate::leanh::LeanObject,
    mut v_bi_1544_: u8,
    mut v_type_1545_: *mut crate::leanh::LeanObject,
    mut v_k_1546_: *mut crate::leanh::LeanObject,
    mut v_kind_1547_: u8,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
    mut v___y_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1558_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1562_: u8 = 0;
    let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1553_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_1553_, 0, v_k_1546_);
                v___x_1554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_1543_,
                    v_bi_1544_,
                    v_type_1545_,
                    v___f_1553_,
                    v_kind_1547_,
                    v___y_1548_,
                    v___y_1549_,
                    v___y_1550_,
                    v___y_1551_,
                );
                if crate::leanh::lean_obj_tag(v___x_1554_) == 0 {
                    v_a_1555_ = crate::leanh::lean_ctor_get(v___x_1554_, 0);
                    v_isSharedCheck_1562_ = (!crate::leanh::lean_is_exclusive(v___x_1554_)) as u8;
                    if v_isSharedCheck_1562_ == 0 {
                        v___x_1557_ = v___x_1554_;
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1555_);
                        crate::leanh::lean_dec(v___x_1554_);
                        v___x_1557_ = crate::leanh::lean_box(0);
                        v_isShared_1558_ = v_isSharedCheck_1562_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1563_ = crate::leanh::lean_ctor_get(v___x_1554_, 0);
                    v_isSharedCheck_1570_ = (!crate::leanh::lean_is_exclusive(v___x_1554_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1565_ = v___x_1554_;
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1563_);
                        crate::leanh::lean_dec(v___x_1554_);
                        v___x_1565_ = crate::leanh::lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1570_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1558_ == 0 {
                    v___x_1560_ = v___x_1557_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
                    v___x_1560_ = v_reuseFailAlloc_1561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1560_;
            }
            3 => {
                if v_isShared_1566_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg___boxed(
    mut v_name_1571_: *mut crate::leanh::LeanObject,
    mut v_bi_1572_: *mut crate::leanh::LeanObject,
    mut v_type_1573_: *mut crate::leanh::LeanObject,
    mut v_k_1574_: *mut crate::leanh::LeanObject,
    mut v_kind_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
    mut v___y_1579_: *mut crate::leanh::LeanObject,
    mut v___y_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_1581_: u8 = 0;
    let mut v_kind_boxed_1582_: u8 = 0;
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1581_ = (crate::leanh::lean_unbox(v_bi_1572_) as u8);
    v_kind_boxed_1582_ = (crate::leanh::lean_unbox(v_kind_1575_) as u8);
    v_res_1583_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1571_, v_bi_boxed_1581_, v_type_1573_, v_k_1574_, v_kind_boxed_1582_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
    crate::leanh::lean_dec(v___y_1579_);
    crate::leanh::lean_dec_ref(v___y_1578_);
    crate::leanh::lean_dec(v___y_1577_);
    crate::leanh::lean_dec_ref(v___y_1576_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(
    mut v_name_1584_: *mut crate::leanh::LeanObject,
    mut v_type_1585_: *mut crate::leanh::LeanObject,
    mut v_k_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = 0;
    v___x_1593_ = 0;
    v___x_1594_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_1584_, v___x_1592_, v_type_1585_, v_k_1586_, v___x_1593_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg___boxed(
    mut v_name_1595_: *mut crate::leanh::LeanObject,
    mut v_type_1596_: *mut crate::leanh::LeanObject,
    mut v_k_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(
        v_name_1595_,
        v_type_1596_,
        v_k_1597_,
        v___y_1598_,
        v___y_1599_,
        v___y_1600_,
        v___y_1601_,
    );
    crate::leanh::lean_dec(v___y_1601_);
    crate::leanh::lean_dec_ref(v___y_1600_);
    crate::leanh::lean_dec(v___y_1599_);
    crate::leanh::lean_dec_ref(v___y_1598_);
    return v_res_1603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_as_1605_: *mut crate::leanh::LeanObject,
    mut v_i_1606_: usize,
    mut v_stop_1607_: usize,
) -> u8 {
    let mut v___x_1608_: u8 = 0;
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: usize = 0;
    let mut v___x_1614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1608_ = lean_usize_dec_eq(v_i_1606_, v_stop_1607_);
                if v___x_1608_ == 0 {
                    v___x_1609_ = lean_array_uget_borrowed(v_as_1605_, v_i_1606_);
                    v___x_1610_ = l_Lean_instBEqMVarId_beq(v_a_1604_, v___x_1609_);
                    if v___x_1610_ == 0 {
                        v___x_1611_ = 1usize;
                        v___x_1612_ = lean_usize_add(v_i_1606_, v___x_1611_);
                        v_i_1606_ = v___x_1612_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1610_;
                    }
                } else {
                    v___x_1614_ = 0;
                    return v___x_1614_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6___boxed(
    mut v_a_1615_: *mut crate::leanh::LeanObject,
    mut v_as_1616_: *mut crate::leanh::LeanObject,
    mut v_i_1617_: *mut crate::leanh::LeanObject,
    mut v_stop_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1619_: usize = 0;
    let mut v_stop_boxed_1620_: usize = 0;
    let mut v_res_1621_: u8 = 0;
    let mut v_r_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1619_ = crate::leanh::lean_unbox_usize(v_i_1617_);
    crate::leanh::lean_dec(v_i_1617_);
    v_stop_boxed_1620_ = crate::leanh::lean_unbox_usize(v_stop_1618_);
    crate::leanh::lean_dec(v_stop_1618_);
    v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_1615_, v_as_1616_, v_i_boxed_1619_, v_stop_boxed_1620_);
    crate::leanh::lean_dec_ref(v_as_1616_);
    crate::leanh::lean_dec(v_a_1615_);
    v_r_1622_ = crate::leanh::lean_box((v_res_1621_) as usize);
    return v_r_1622_;
}
pub unsafe fn l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(
    mut v_as_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    v___x_1625_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1626_ = lean_array_get_size(v_as_1623_);
    v___x_1627_ = lean_nat_dec_lt(v___x_1625_, v___x_1626_);
    if v___x_1627_ == 0 {
        return v___x_1627_;
    } else {
        if v___x_1627_ == 0 {
            return v___x_1627_;
        } else {
            let mut v___x_1628_: usize = 0;
            let mut v___x_1629_: usize = 0;
            let mut v___x_1630_: u8 = 0;
            v___x_1628_ = 0usize;
            v___x_1629_ = lean_usize_of_nat(v___x_1626_);
            v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_MVarId_rewrite_spec__4_spec__6(v_a_1624_, v_as_1623_, v___x_1628_, v___x_1629_);
            return v___x_1630_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_MVarId_rewrite_spec__4___boxed(
    mut v_as_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1633_: u8 = 0;
    let mut v_r_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(v_as_1631_, v_a_1632_);
    crate::leanh::lean_dec(v_a_1632_);
    crate::leanh::lean_dec_ref(v_as_1631_);
    v_r_1634_ = crate::leanh::lean_box((v_res_1633_) as usize);
    return v_r_1634_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_as_1636_: *mut crate::leanh::LeanObject,
    mut v_i_1637_: usize,
    mut v_stop_1638_: usize,
    mut v_b_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1645_: u8 = 0;
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1645_ = lean_usize_dec_eq(v_i_1637_, v_stop_1638_);
                if v___x_1645_ == 0 {
                    v___x_1646_ = lean_array_uget_borrowed(v_as_1636_, v_i_1637_);
                    v___x_1647_ = l_Array_contains___at___00Lean_MVarId_rewrite_spec__4(
                        v_a_1635_,
                        v___x_1646_,
                    );
                    if v___x_1647_ == 0 {
                        crate::leanh::lean_inc(v___x_1646_);
                        v___x_1648_ = lean_array_push(v_b_1639_, v___x_1646_);
                        v___y_1641_ = v___x_1648_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1641_ = v_b_1639_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1639_;
                }
            }
            1 => {
                v___x_1642_ = 1usize;
                v___x_1643_ = lean_usize_add(v_i_1637_, v___x_1642_);
                v_i_1637_ = v___x_1643_;
                v_b_1639_ = v___y_1641_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5___boxed(
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_as_1650_: *mut crate::leanh::LeanObject,
    mut v_i_1651_: *mut crate::leanh::LeanObject,
    mut v_stop_1652_: *mut crate::leanh::LeanObject,
    mut v_b_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1654_: usize = 0;
    let mut v_stop_boxed_1655_: usize = 0;
    let mut v_res_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1654_ = crate::leanh::lean_unbox_usize(v_i_1651_);
    crate::leanh::lean_dec(v_i_1651_);
    v_stop_boxed_1655_ = crate::leanh::lean_unbox_usize(v_stop_1652_);
    crate::leanh::lean_dec(v_stop_1652_);
    v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_1649_, v_as_1650_, v_i_boxed_1654_, v_stop_boxed_1655_, v_b_1653_);
    crate::leanh::lean_dec_ref(v_as_1650_);
    crate::leanh::lean_dec_ref(v_a_1649_);
    return v_res_1656_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(
    mut v_msgData_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = lean_st_ref_get(v___y_1661_);
    v_env_1664_ = crate::leanh::lean_ctor_get(v___x_1663_, 0);
    crate::leanh::lean_inc_ref(v_env_1664_);
    crate::leanh::lean_dec(v___x_1663_);
    v___x_1665_ = lean_st_ref_get(v___y_1659_);
    v_mctx_1666_ = crate::leanh::lean_ctor_get(v___x_1665_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1666_);
    crate::leanh::lean_dec(v___x_1665_);
    v_lctx_1667_ = crate::leanh::lean_ctor_get(v___y_1658_, 2);
    v_options_1668_ = crate::leanh::lean_ctor_get(v___y_1660_, 2);
    crate::leanh::lean_inc_ref(v_options_1668_);
    crate::leanh::lean_inc_ref(v_lctx_1667_);
    v___x_1669_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1669_, 0, v_env_1664_);
    crate::leanh::lean_ctor_set(v___x_1669_, 1, v_mctx_1666_);
    crate::leanh::lean_ctor_set(v___x_1669_, 2, v_lctx_1667_);
    crate::leanh::lean_ctor_set(v___x_1669_, 3, v_options_1668_);
    v___x_1670_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1669_);
    crate::leanh::lean_ctor_set(v___x_1670_, 1, v_msgData_1657_);
    v___x_1671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3___boxed(
    mut v_msgData_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msgData_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
    crate::leanh::lean_dec(v___y_1676_);
    crate::leanh::lean_dec_ref(v___y_1675_);
    crate::leanh::lean_dec(v___y_1674_);
    crate::leanh::lean_dec_ref(v___y_1673_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(
    mut v_msg_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1685_ = crate::leanh::lean_ctor_get(v___y_1682_, 5);
                v___x_1686_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_rewrite_spec__2_spec__3(v_msg_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
                v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1686_, 0);
                v_isSharedCheck_1695_ = (!crate::leanh::lean_is_exclusive(v___x_1686_)) as u8;
                if v_isSharedCheck_1695_ == 0 {
                    v___x_1689_ = v___x_1686_;
                    v_isShared_1690_ = v_isSharedCheck_1695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1687_);
                    crate::leanh::lean_dec(v___x_1686_);
                    v___x_1689_ = crate::leanh::lean_box(0);
                    v_isShared_1690_ = v_isSharedCheck_1695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1685_);
                v___x_1691_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1691_, 0, v_ref_1685_);
                crate::leanh::lean_ctor_set(v___x_1691_, 1, v_a_1687_);
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1689_, 1);
                    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1691_);
                    v___x_1693_ = v___x_1689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1691_);
                    v___x_1693_ = v_reuseFailAlloc_1694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg___boxed(
    mut v_msg_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(
        v_msg_1696_,
        v___y_1697_,
        v___y_1698_,
        v___y_1699_,
        v___y_1700_,
    );
    crate::leanh::lean_dec(v___y_1700_);
    crate::leanh::lean_dec_ref(v___y_1699_);
    crate::leanh::lean_dec(v___y_1698_);
    crate::leanh::lean_dec_ref(v___y_1697_);
    return v_res_1702_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = l_Lean_MVarId_rewrite___lam__1___closed__0;
    v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_Lean_MVarId_rewrite___lam__1___closed__2;
    v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Lean_MVarId_rewrite___lam__1___closed__7;
    v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1718_ = l_Lean_MVarId_rewrite___lam__1___closed__9;
    v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_MVarId_rewrite___lam__1___closed__11;
    v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Lean_MVarId_rewrite___lam__1___closed__13;
    v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Lean_MVarId_rewrite___lam__1___closed__15;
    v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
    return v___x_1728_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Lean_MVarId_rewrite___lam__1___closed__17;
    v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
    return v___x_1731_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Lean_MVarId_rewrite___lam__1___closed__19;
    v___x_1734_ = l_Lean_stringToMessageData(v___x_1733_);
    return v___x_1734_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Lean_MVarId_rewrite___lam__1___closed__24;
    v___x_1742_ = l_Lean_stringToMessageData(v___x_1741_);
    return v___x_1742_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_MVarId_rewrite___lam__1___closed__28;
    v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = l_Lean_MVarId_rewrite___lam__1___closed__32;
    v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__35() -> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lean_MVarId_rewrite___lam__1___closed__34;
    v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__37() -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = l_Lean_MVarId_rewrite___lam__1___closed__36;
    v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__39() -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = l_Lean_MVarId_rewrite___lam__1___closed__38;
    v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
    return v___x_1763_;
}
pub unsafe fn _init_l_Lean_MVarId_rewrite___lam__1___closed__46() -> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ = crate::leanh::lean_box(0);
    v___x_1773_ = l_Lean_MVarId_rewrite___lam__1___closed__45;
    v___x_1774_ = l_Lean_mkConst(v___x_1773_, v___x_1772_);
    return v___x_1774_;
}
pub unsafe fn l_Lean_MVarId_rewrite___lam__1(
    mut v_mvarId_1775_: *mut crate::leanh::LeanObject,
    mut v___x_1776_: *mut crate::leanh::LeanObject,
    mut v_heq_1777_: *mut crate::leanh::LeanObject,
    mut v_e_1778_: *mut crate::leanh::LeanObject,
    mut v_config_1779_: *mut crate::leanh::LeanObject,
    mut v_symm_1780_: u8,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
    mut v___y_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v_fst_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___y_1837_: usize = 0;
    let mut v___y_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: usize = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1864_: u8 = 0;
    let mut v_a_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v___y_1874_: usize = 0;
    let mut v___y_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v___y_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1899_: u8 = 0;
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1902_: usize = 0;
    let mut v___x_1903_: usize = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: usize = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: usize = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut v___y_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: u8 = 0;
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1956_: u8 = 0;
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1960_: u8 = 0;
    let mut v_a_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v___y_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_reuseFailAlloc_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_a_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v___y_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2046_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eNew_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: u8 = 0;
    let mut v_a_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut v___y_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2130_: u8 = 0;
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v_transparency_2145_: u8 = 0;
    let mut v_offsetCnstrs_2146_: u8 = 0;
    let mut v_occs_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2149_: u8 = 0;
    let mut v_ctxApprox_2150_: u8 = 0;
    let mut v_quasiPatternApprox_2151_: u8 = 0;
    let mut v_constApprox_2152_: u8 = 0;
    let mut v_isDefEqStuckEx_2153_: u8 = 0;
    let mut v_unificationHints_2154_: u8 = 0;
    let mut v_proofIrrelevance_2155_: u8 = 0;
    let mut v_assignSyntheticOpaque_2156_: u8 = 0;
    let mut v_etaStruct_2157_: u8 = 0;
    let mut v_univApprox_2158_: u8 = 0;
    let mut v_iota_2159_: u8 = 0;
    let mut v_beta_2160_: u8 = 0;
    let mut v_proj_2161_: u8 = 0;
    let mut v_zeta_2162_: u8 = 0;
    let mut v_zetaDelta_2163_: u8 = 0;
    let mut v_zetaUnused_2164_: u8 = 0;
    let mut v_zetaHave_2165_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v_trackZetaDelta_2169_: u8 = 0;
    let mut v_zetaDeltaSet_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2176_: u8 = 0;
    let mut v_inTypeClassResolution_2177_: u8 = 0;
    let mut v_cacheInferType_2178_: u8 = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u64 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2193_: u8 = 0;
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_reuseFailAlloc_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut v_a_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2223_: u8 = 0;
    let mut v_a_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2231_: u8 = 0;
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut v_isSharedCheck_2234_: u8 = 0;
    let mut v___y_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_heq_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_heqType_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_heq_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_heqType_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v_val_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_a_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2335_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2339_: u8 = 0;
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v_a_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_1776_);
                crate::leanh::lean_inc(v_mvarId_1775_);
                v___x_1814_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1775_,
                    v___x_1776_,
                    v___y_1781_,
                    v___y_1782_,
                    v___y_1783_,
                    v___y_1784_,
                );
                if crate::leanh::lean_obj_tag(v___x_1814_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1814_, 1);
                    crate::leanh::lean_inc(v___y_1784_);
                    crate::leanh::lean_inc_ref(v___y_1783_);
                    crate::leanh::lean_inc(v___y_1782_);
                    crate::leanh::lean_inc_ref(v___y_1781_);
                    crate::leanh::lean_inc_ref(v_heq_1777_);
                    v___x_1815_ = lean_infer_type(
                        v_heq_1777_,
                        v___y_1781_,
                        v___y_1782_,
                        v___y_1783_,
                        v___y_1784_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1815_) == 0 {
                        v_a_1816_ = crate::leanh::lean_ctor_get(v___x_1815_, 0);
                        crate::leanh::lean_inc(v_a_1816_);
                        crate::leanh::lean_dec_ref_known(v___x_1815_, 1);
                        v___x_1817_ =
                            l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
                                v_a_1816_,
                                v___y_1782_,
                            );
                        v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
                        v_isSharedCheck_2350_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1817_)) as u8;
                        if v_isSharedCheck_2350_ == 0 {
                            v___x_1820_ = v___x_1817_;
                            v_isShared_1821_ = v_isSharedCheck_2350_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1818_);
                            crate::leanh::lean_dec(v___x_1817_);
                            v___x_1820_ = crate::leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_2350_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_1784_);
                        crate::leanh::lean_dec_ref(v___y_1783_);
                        crate::leanh::lean_dec(v___y_1782_);
                        crate::leanh::lean_dec_ref(v___y_1781_);
                        crate::leanh::lean_dec_ref(v_config_1779_);
                        crate::leanh::lean_dec_ref(v_e_1778_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        v_a_2351_ = crate::leanh::lean_ctor_get(v___x_1815_, 0);
                        v_isSharedCheck_2358_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1815_)) as u8;
                        if v_isSharedCheck_2358_ == 0 {
                            v___x_2353_ = v___x_1815_;
                            v_isShared_2354_ = v_isSharedCheck_2358_;
                            state = 68;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2351_);
                            crate::leanh::lean_dec(v___x_1815_);
                            v___x_2353_ = crate::leanh::lean_box(0);
                            v_isShared_2354_ = v_isSharedCheck_2358_;
                            state = 68;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1784_);
                    crate::leanh::lean_dec_ref(v___y_1783_);
                    crate::leanh::lean_dec(v___y_1782_);
                    crate::leanh::lean_dec_ref(v___y_1781_);
                    crate::leanh::lean_dec_ref(v_config_1779_);
                    crate::leanh::lean_dec_ref(v_e_1778_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2359_ = crate::leanh::lean_ctor_get(v___x_1814_, 0);
                    v_isSharedCheck_2366_ = (!crate::leanh::lean_is_exclusive(v___x_1814_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v___x_2361_ = v___x_1814_;
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 70;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2359_);
                        crate::leanh::lean_dec(v___x_1814_);
                        v___x_2361_ = crate::leanh::lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2366_;
                        state = 70;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1794_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__1_once),
                    _init_l_Lean_MVarId_rewrite___lam__1___closed__1,
                );
                v___x_1795_ = crate::leanh::lean_unsigned_to_nat(30);
                v___x_1796_ = l_Lean_inlineExpr(v___y_1792_, v___x_1795_);
                v___x_1797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1797_, 0, v___x_1794_);
                crate::leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                v___x_1798_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__3_once),
                    _init_l_Lean_MVarId_rewrite___lam__1___closed__3,
                );
                v___x_1799_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1799_, 0, v___x_1797_);
                crate::leanh::lean_ctor_set(v___x_1799_, 1, v___x_1798_);
                crate::leanh::lean_inc_ref(v___y_1793_);
                v___x_1800_ = l_Lean_stringToMessageData(v___y_1793_);
                v___x_1801_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1799_);
                crate::leanh::lean_ctor_set(v___x_1801_, 1, v___x_1800_);
                v___x_1802_ = l_Lean_indentExpr(v___y_1789_);
                v___x_1803_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1801_);
                crate::leanh::lean_ctor_set(v___x_1803_, 1, v___x_1802_);
                v___x_1804_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(
                    v___x_1803_,
                    v___y_1791_,
                    v___y_1790_,
                    v___y_1788_,
                    v___y_1787_,
                );
                crate::leanh::lean_dec(v___y_1787_);
                crate::leanh::lean_dec_ref(v___y_1788_);
                crate::leanh::lean_dec(v___y_1790_);
                crate::leanh::lean_dec_ref(v___y_1791_);
                return v___x_1804_;
            }
            2 => {
                v___x_1810_ = l_Array_append___redArg(v___y_1807_, v___y_1809_);
                crate::leanh::lean_dec_ref(v___y_1809_);
                v___x_1811_ = lean_array_to_list(v___x_1810_);
                v___x_1812_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1812_, 0, v___y_1806_);
                crate::leanh::lean_ctor_set(v___x_1812_, 1, v___y_1808_);
                crate::leanh::lean_ctor_set(v___x_1812_, 2, v___x_1811_);
                v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1812_);
                return v___x_1813_;
            }
            3 => {
                v___x_1822_ = crate::leanh::lean_box(0);
                v___x_1823_ = 0;
                v___x_1824_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_a_1818_,
                    v___x_1822_,
                    v___x_1823_,
                    v___y_1781_,
                    v___y_1782_,
                    v___y_1783_,
                    v___y_1784_,
                );
                if crate::leanh::lean_obj_tag(v___x_1824_) == 0 {
                    v_a_1825_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                    crate::leanh::lean_inc(v_a_1825_);
                    crate::leanh::lean_dec_ref_known(v___x_1824_, 1);
                    v_snd_1826_ = crate::leanh::lean_ctor_get(v_a_1825_, 1);
                    v_fst_1827_ = crate::leanh::lean_ctor_get(v_a_1825_, 0);
                    v_isSharedCheck_2341_ = (!crate::leanh::lean_is_exclusive(v_a_1825_)) as u8;
                    if v_isSharedCheck_2341_ == 0 {
                        v___x_1829_ = v_a_1825_;
                        v_isShared_1830_ = v_isSharedCheck_2341_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1826_);
                        crate::leanh::lean_inc(v_fst_1827_);
                        crate::leanh::lean_dec(v_a_1825_);
                        v___x_1829_ = crate::leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_2341_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec(v___y_1784_);
                    crate::leanh::lean_dec_ref(v___y_1783_);
                    crate::leanh::lean_dec(v___y_1782_);
                    crate::leanh::lean_dec_ref(v___y_1781_);
                    crate::leanh::lean_dec_ref(v_config_1779_);
                    crate::leanh::lean_dec_ref(v_e_1778_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2342_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                    v_isSharedCheck_2349_ = (!crate::leanh::lean_is_exclusive(v___x_1824_)) as u8;
                    if v_isSharedCheck_2349_ == 0 {
                        v___x_2344_ = v___x_1824_;
                        v_isShared_2345_ = v_isSharedCheck_2349_;
                        state = 66;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2342_);
                        crate::leanh::lean_dec(v___x_1824_);
                        v___x_2344_ = crate::leanh::lean_box(0);
                        v_isShared_2345_ = v_isSharedCheck_2349_;
                        state = 66;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_1831_ = crate::leanh::lean_ctor_get(v_snd_1826_, 0);
                v_snd_1832_ = crate::leanh::lean_ctor_get(v_snd_1826_, 1);
                v_isSharedCheck_2340_ = (!crate::leanh::lean_is_exclusive(v_snd_1826_)) as u8;
                if v_isSharedCheck_2340_ == 0 {
                    v___x_1834_ = v_snd_1826_;
                    v_isShared_1835_ = v_isSharedCheck_2340_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1832_);
                    crate::leanh::lean_inc(v_fst_1831_);
                    crate::leanh::lean_dec(v_snd_1826_);
                    v___x_1834_ = crate::leanh::lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_2340_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_heq_1777_);
                v___x_2321_ = l_Lean_mkAppN(v_heq_1777_, v_fst_1827_);
                v___x_2322_ = l_Lean_MVarId_rewrite___lam__1___closed__43;
                v___x_2323_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2324_ = l_Lean_Expr_isAppOfArity(v_snd_1832_, v___x_2322_, v___x_2323_);
                if v___x_2324_ == 0 {
                    v_heq_2264_ = v___x_2321_;
                    v_heqType_2265_ = v_snd_1832_;
                    v___y_2266_ = v___y_1781_;
                    v___y_2267_ = v___y_1782_;
                    v___y_2268_ = v___y_1783_;
                    v___y_2269_ = v___y_1784_;
                    state = 55;
                    continue;
                } else {
                    v___x_2325_ = l_Lean_Expr_appFn_x21(v_snd_1832_);
                    v___x_2326_ = l_Lean_Expr_appArg_x21(v___x_2325_);
                    crate::leanh::lean_dec_ref(v___x_2325_);
                    v___x_2327_ = l_Lean_Expr_appArg_x21(v_snd_1832_);
                    crate::leanh::lean_dec(v_snd_1832_);
                    crate::leanh::lean_inc_ref(v___x_2327_);
                    crate::leanh::lean_inc_ref(v___x_2326_);
                    v___x_2328_ = l_Lean_Meta_mkEq(
                        v___x_2326_,
                        v___x_2327_,
                        v___y_1781_,
                        v___y_1782_,
                        v___y_1783_,
                        v___y_1784_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2328_) == 0 {
                        v_a_2329_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                        crate::leanh::lean_inc(v_a_2329_);
                        crate::leanh::lean_dec_ref_known(v___x_2328_, 1);
                        v___x_2330_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__46),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_rewrite___lam__1___closed__46_once
                            ),
                            _init_l_Lean_MVarId_rewrite___lam__1___closed__46,
                        );
                        v___x_2331_ =
                            l_Lean_mkApp3(v___x_2330_, v___x_2326_, v___x_2327_, v___x_2321_);
                        v_heq_2264_ = v___x_2331_;
                        v_heqType_2265_ = v_a_2329_;
                        v___y_2266_ = v___y_1781_;
                        v___y_2267_ = v___y_1782_;
                        v___y_2268_ = v___y_1783_;
                        v___y_2269_ = v___y_1784_;
                        state = 55;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2327_);
                        crate::leanh::lean_dec_ref(v___x_2326_);
                        crate::leanh::lean_dec_ref(v___x_2321_);
                        crate::leanh::lean_del_object(v___x_1834_);
                        crate::leanh::lean_dec(v_fst_1831_);
                        crate::leanh::lean_del_object(v___x_1829_);
                        crate::leanh::lean_dec(v_fst_1827_);
                        crate::leanh::lean_del_object(v___x_1820_);
                        crate::leanh::lean_dec(v___y_1784_);
                        crate::leanh::lean_dec_ref(v___y_1783_);
                        crate::leanh::lean_dec(v___y_1782_);
                        crate::leanh::lean_dec_ref(v___y_1781_);
                        crate::leanh::lean_dec_ref(v_config_1779_);
                        crate::leanh::lean_dec_ref(v_e_1778_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        v_a_2332_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                        v_isSharedCheck_2339_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2328_)) as u8;
                        if v_isSharedCheck_2339_ == 0 {
                            v___x_2334_ = v___x_2328_;
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2332_);
                            crate::leanh::lean_dec(v___x_2328_);
                            v___x_2334_ = crate::leanh::lean_box(0);
                            v_isShared_2335_ = v_isSharedCheck_2339_;
                            state = 64;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_1846_ = l_Lean_Meta_appendParentTag(
                    v_mvarId_1775_,
                    v_fst_1827_,
                    v_fst_1831_,
                    v___y_1839_,
                    v___y_1838_,
                    v___y_1842_,
                    v___y_1840_,
                );
                crate::leanh::lean_dec(v_fst_1831_);
                crate::leanh::lean_dec(v_fst_1827_);
                if crate::leanh::lean_obj_tag(v___x_1846_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1846_, 1);
                    v___x_1847_ = l_Lean_Meta_getMVarsNoDelayed(
                        v_heq_1777_,
                        v___y_1839_,
                        v___y_1838_,
                        v___y_1842_,
                        v___y_1840_,
                    );
                    crate::leanh::lean_dec(v___y_1840_);
                    crate::leanh::lean_dec_ref(v___y_1842_);
                    crate::leanh::lean_dec(v___y_1838_);
                    crate::leanh::lean_dec_ref(v___y_1839_);
                    if crate::leanh::lean_obj_tag(v___x_1847_) == 0 {
                        v_a_1848_ = crate::leanh::lean_ctor_get(v___x_1847_, 0);
                        crate::leanh::lean_inc(v_a_1848_);
                        crate::leanh::lean_dec_ref_known(v___x_1847_, 1);
                        v___x_1849_ = lean_array_get_size(v_a_1848_);
                        v___x_1850_ = lean_mk_empty_array_with_capacity(v___y_1843_);
                        v___x_1851_ = lean_nat_dec_lt(v___y_1843_, v___x_1849_);
                        if v___x_1851_ == 0 {
                            crate::leanh::lean_dec(v_a_1848_);
                            v___y_1806_ = v___y_1841_;
                            v___y_1807_ = v_a_1845_;
                            v___y_1808_ = v___y_1844_;
                            v___y_1809_ = v___x_1850_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1852_ = lean_nat_dec_le(v___x_1849_, v___x_1849_);
                            if v___x_1852_ == 0 {
                                if v___x_1851_ == 0 {
                                    crate::leanh::lean_dec(v_a_1848_);
                                    v___y_1806_ = v___y_1841_;
                                    v___y_1807_ = v_a_1845_;
                                    v___y_1808_ = v___y_1844_;
                                    v___y_1809_ = v___x_1850_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_1853_ = lean_usize_of_nat(v___x_1849_);
                                    v___x_1854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_1845_, v_a_1848_, v___y_1837_, v___x_1853_, v___x_1850_);
                                    crate::leanh::lean_dec(v_a_1848_);
                                    v___y_1806_ = v___y_1841_;
                                    v___y_1807_ = v_a_1845_;
                                    v___y_1808_ = v___y_1844_;
                                    v___y_1809_ = v___x_1854_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_1855_ = lean_usize_of_nat(v___x_1849_);
                                v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__5(v_a_1845_, v_a_1848_, v___y_1837_, v___x_1855_, v___x_1850_);
                                crate::leanh::lean_dec(v_a_1848_);
                                v___y_1806_ = v___y_1841_;
                                v___y_1807_ = v_a_1845_;
                                v___y_1808_ = v___y_1844_;
                                v___y_1809_ = v___x_1856_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1845_);
                        crate::leanh::lean_dec_ref(v___y_1844_);
                        crate::leanh::lean_dec_ref(v___y_1841_);
                        v_a_1857_ = crate::leanh::lean_ctor_get(v___x_1847_, 0);
                        v_isSharedCheck_1864_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1847_)) as u8;
                        if v_isSharedCheck_1864_ == 0 {
                            v___x_1859_ = v___x_1847_;
                            v_isShared_1860_ = v_isSharedCheck_1864_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1857_);
                            crate::leanh::lean_dec(v___x_1847_);
                            v___x_1859_ = crate::leanh::lean_box(0);
                            v_isShared_1860_ = v_isSharedCheck_1864_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_1845_);
                    crate::leanh::lean_dec_ref(v___y_1844_);
                    crate::leanh::lean_dec_ref(v___y_1842_);
                    crate::leanh::lean_dec_ref(v___y_1841_);
                    crate::leanh::lean_dec(v___y_1840_);
                    crate::leanh::lean_dec_ref(v___y_1839_);
                    crate::leanh::lean_dec(v___y_1838_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    v_a_1865_ = crate::leanh::lean_ctor_get(v___x_1846_, 0);
                    v_isSharedCheck_1872_ = (!crate::leanh::lean_is_exclusive(v___x_1846_)) as u8;
                    if v_isSharedCheck_1872_ == 0 {
                        v___x_1867_ = v___x_1846_;
                        v_isShared_1868_ = v_isSharedCheck_1872_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1865_);
                        crate::leanh::lean_dec(v___x_1846_);
                        v___x_1867_ = crate::leanh::lean_box(0);
                        v_isShared_1868_ = v_isSharedCheck_1872_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1860_ == 0 {
                    v___x_1862_ = v___x_1859_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
                    v___x_1862_ = v_reuseFailAlloc_1863_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1862_;
            }
            9 => {
                if v_isShared_1868_ == 0 {
                    v___x_1870_ = v___x_1867_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
                    v___x_1870_ = v_reuseFailAlloc_1871_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1870_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_1882_) == 0 {
                    v_a_1883_ = crate::leanh::lean_ctor_get(v___y_1882_, 0);
                    crate::leanh::lean_inc(v_a_1883_);
                    crate::leanh::lean_dec_ref_known(v___y_1882_, 1);
                    v___y_1837_ = v___y_1874_;
                    v___y_1838_ = v___y_1876_;
                    v___y_1839_ = v___y_1875_;
                    v___y_1840_ = v___y_1877_;
                    v___y_1841_ = v___y_1879_;
                    v___y_1842_ = v___y_1878_;
                    v___y_1843_ = v___y_1880_;
                    v___y_1844_ = v___y_1881_;
                    v_a_1845_ = v_a_1883_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1881_);
                    crate::leanh::lean_dec_ref(v___y_1879_);
                    crate::leanh::lean_dec_ref(v___y_1878_);
                    crate::leanh::lean_dec(v___y_1877_);
                    crate::leanh::lean_dec(v___y_1876_);
                    crate::leanh::lean_dec_ref(v___y_1875_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_1884_ = crate::leanh::lean_ctor_get(v___y_1882_, 0);
                    v_isSharedCheck_1891_ = (!crate::leanh::lean_is_exclusive(v___y_1882_)) as u8;
                    if v_isSharedCheck_1891_ == 0 {
                        v___x_1886_ = v___y_1882_;
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1884_);
                        crate::leanh::lean_dec(v___y_1882_);
                        v___x_1886_ = crate::leanh::lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1891_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_1887_ == 0 {
                    v___x_1889_ = v___x_1886_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1889_;
            }
            14 => {
                v___x_1900_ = 0;
                crate::leanh::lean_inc(v_fst_1831_);
                crate::leanh::lean_inc(v_mvarId_1775_);
                v___x_1901_ = l_Lean_Meta_postprocessAppMVars(
                    v___x_1776_,
                    v_mvarId_1775_,
                    v_fst_1827_,
                    v_fst_1831_,
                    v___y_1899_,
                    v___x_1900_,
                    v___y_1894_,
                    v___y_1893_,
                    v___y_1897_,
                    v___y_1895_,
                );
                if crate::leanh::lean_obj_tag(v___x_1901_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1901_, 1);
                    v_sz_1902_ = lean_array_size(v_fst_1827_);
                    v___x_1903_ = 0usize;
                    crate::leanh::lean_inc(v_fst_1827_);
                    v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_rewrite_spec__3(v_sz_1902_, v___x_1903_, v_fst_1827_);
                    v___x_1905_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1906_ = lean_array_get_size(v___x_1904_);
                    v___x_1907_ = l_Lean_MVarId_rewrite___lam__1___closed__4;
                    v___x_1908_ = lean_nat_dec_lt(v___x_1905_, v___x_1906_);
                    if v___x_1908_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1904_);
                        v___y_1837_ = v___x_1903_;
                        v___y_1838_ = v___y_1893_;
                        v___y_1839_ = v___y_1894_;
                        v___y_1840_ = v___y_1895_;
                        v___y_1841_ = v___y_1896_;
                        v___y_1842_ = v___y_1897_;
                        v___y_1843_ = v___x_1905_;
                        v___y_1844_ = v___y_1898_;
                        v_a_1845_ = v___x_1907_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1909_ = lean_nat_dec_le(v___x_1906_, v___x_1906_);
                        if v___x_1909_ == 0 {
                            if v___x_1908_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1904_);
                                v___y_1837_ = v___x_1903_;
                                v___y_1838_ = v___y_1893_;
                                v___y_1839_ = v___y_1894_;
                                v___y_1840_ = v___y_1895_;
                                v___y_1841_ = v___y_1896_;
                                v___y_1842_ = v___y_1897_;
                                v___y_1843_ = v___x_1905_;
                                v___y_1844_ = v___y_1898_;
                                v_a_1845_ = v___x_1907_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1910_ = lean_usize_of_nat(v___x_1906_);
                                v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_1904_, v___x_1903_, v___x_1910_, v___x_1907_, v___y_1894_, v___y_1893_, v___y_1897_, v___y_1895_);
                                crate::leanh::lean_dec_ref(v___x_1904_);
                                v___y_1874_ = v___x_1903_;
                                v___y_1875_ = v___y_1894_;
                                v___y_1876_ = v___y_1893_;
                                v___y_1877_ = v___y_1895_;
                                v___y_1878_ = v___y_1897_;
                                v___y_1879_ = v___y_1896_;
                                v___y_1880_ = v___x_1905_;
                                v___y_1881_ = v___y_1898_;
                                v___y_1882_ = v___x_1911_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v___x_1912_ = lean_usize_of_nat(v___x_1906_);
                            v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_rewrite_spec__6(v___x_1904_, v___x_1903_, v___x_1912_, v___x_1907_, v___y_1894_, v___y_1893_, v___y_1897_, v___y_1895_);
                            crate::leanh::lean_dec_ref(v___x_1904_);
                            v___y_1874_ = v___x_1903_;
                            v___y_1875_ = v___y_1894_;
                            v___y_1876_ = v___y_1893_;
                            v___y_1877_ = v___y_1895_;
                            v___y_1878_ = v___y_1897_;
                            v___y_1879_ = v___y_1896_;
                            v___y_1880_ = v___x_1905_;
                            v___y_1881_ = v___y_1898_;
                            v___y_1882_ = v___x_1913_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1898_);
                    crate::leanh::lean_dec_ref(v___y_1897_);
                    crate::leanh::lean_dec_ref(v___y_1896_);
                    crate::leanh::lean_dec(v___y_1895_);
                    crate::leanh::lean_dec_ref(v___y_1894_);
                    crate::leanh::lean_dec(v___y_1893_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_1914_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                    v_isSharedCheck_1921_ = (!crate::leanh::lean_is_exclusive(v___x_1901_)) as u8;
                    if v_isSharedCheck_1921_ == 0 {
                        v___x_1916_ = v___x_1901_;
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1914_);
                        crate::leanh::lean_dec(v___x_1901_);
                        v___x_1916_ = crate::leanh::lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_1917_ == 0 {
                    v___x_1919_ = v___x_1916_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
                    v___x_1919_ = v_reuseFailAlloc_1920_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1919_;
            }
            17 => {
                crate::leanh::lean_inc_ref(v___y_1927_);
                v___x_1934_ = l_Lean_Meta_getLevel(
                    v___y_1927_,
                    v___y_1930_,
                    v___y_1931_,
                    v___y_1932_,
                    v___y_1933_,
                );
                if crate::leanh::lean_obj_tag(v___x_1934_) == 0 {
                    v_a_1935_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                    crate::leanh::lean_inc(v_a_1935_);
                    crate::leanh::lean_dec_ref_known(v___x_1934_, 1);
                    crate::leanh::lean_inc_ref(v___y_1929_);
                    v___x_1936_ = l_Lean_Meta_getLevel(
                        v___y_1929_,
                        v___y_1930_,
                        v___y_1931_,
                        v___y_1932_,
                        v___y_1933_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1936_) == 0 {
                        v_a_1937_ = crate::leanh::lean_ctor_get(v___x_1936_, 0);
                        crate::leanh::lean_inc(v_a_1937_);
                        crate::leanh::lean_dec_ref_known(v___x_1936_, 1);
                        v_options_1938_ = crate::leanh::lean_ctor_get(v___y_1932_, 2);
                        v___x_1939_ = l_Lean_MVarId_rewrite___lam__1___closed__6;
                        v___x_1940_ = crate::leanh::lean_box(0);
                        if v_isShared_1835_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1834_, 1);
                            crate::leanh::lean_ctor_set(v___x_1834_, 1, v___x_1940_);
                            crate::leanh::lean_ctor_set(v___x_1834_, 0, v_a_1937_);
                            v___x_1942_ = v___x_1834_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_1952_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1937_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1940_);
                            v___x_1942_ = v_reuseFailAlloc_1952_;
                            state = 18;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1935_);
                        crate::leanh::lean_dec(v___y_1933_);
                        crate::leanh::lean_dec_ref(v___y_1932_);
                        crate::leanh::lean_dec(v___y_1931_);
                        crate::leanh::lean_dec_ref(v___y_1930_);
                        crate::leanh::lean_dec_ref(v___y_1929_);
                        crate::leanh::lean_dec_ref(v___y_1928_);
                        crate::leanh::lean_dec_ref(v___y_1927_);
                        crate::leanh::lean_dec_ref(v___y_1926_);
                        crate::leanh::lean_dec_ref(v___y_1925_);
                        crate::leanh::lean_dec_ref(v___y_1924_);
                        crate::leanh::lean_dec_ref(v___y_1923_);
                        crate::leanh::lean_del_object(v___x_1834_);
                        crate::leanh::lean_dec(v_fst_1831_);
                        crate::leanh::lean_del_object(v___x_1829_);
                        crate::leanh::lean_dec(v_fst_1827_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        v_a_1953_ = crate::leanh::lean_ctor_get(v___x_1936_, 0);
                        v_isSharedCheck_1960_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1936_)) as u8;
                        if v_isSharedCheck_1960_ == 0 {
                            v___x_1955_ = v___x_1936_;
                            v_isShared_1956_ = v_isSharedCheck_1960_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1953_);
                            crate::leanh::lean_dec(v___x_1936_);
                            v___x_1955_ = crate::leanh::lean_box(0);
                            v_isShared_1956_ = v_isSharedCheck_1960_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1933_);
                    crate::leanh::lean_dec_ref(v___y_1932_);
                    crate::leanh::lean_dec(v___y_1931_);
                    crate::leanh::lean_dec_ref(v___y_1930_);
                    crate::leanh::lean_dec_ref(v___y_1929_);
                    crate::leanh::lean_dec_ref(v___y_1928_);
                    crate::leanh::lean_dec_ref(v___y_1927_);
                    crate::leanh::lean_dec_ref(v___y_1926_);
                    crate::leanh::lean_dec_ref(v___y_1925_);
                    crate::leanh::lean_dec_ref(v___y_1924_);
                    crate::leanh::lean_dec_ref(v___y_1923_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_1961_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                    v_isSharedCheck_1968_ = (!crate::leanh::lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1968_ == 0 {
                        v___x_1963_ = v___x_1934_;
                        v_isShared_1964_ = v_isSharedCheck_1968_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1961_);
                        crate::leanh::lean_dec(v___x_1934_);
                        v___x_1963_ = crate::leanh::lean_box(0);
                        v_isShared_1964_ = v_isSharedCheck_1968_;
                        state = 22;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_1830_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1829_, 1);
                    crate::leanh::lean_ctor_set(v___x_1829_, 1, v___x_1942_);
                    crate::leanh::lean_ctor_set(v___x_1829_, 0, v_a_1935_);
                    v___x_1944_ = v___x_1829_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1942_);
                    v___x_1944_ = v_reuseFailAlloc_1951_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_1945_ = l_Lean_Expr_const___override(v___x_1939_, v___x_1944_);
                v___x_1946_ = l_Lean_mkApp6(
                    v___x_1945_,
                    v___y_1927_,
                    v___y_1929_,
                    v___y_1928_,
                    v___y_1924_,
                    v___y_1923_,
                    v___y_1925_,
                );
                v___x_1947_ = l_Lean_Meta_tactic_skipAssignedInstances;
                v___x_1948_ = l_Lean_Option_get___at___00Lean_MVarId_rewrite_spec__7(
                    v_options_1938_,
                    v___x_1947_,
                );
                if v___x_1948_ == 0 {
                    v___x_1949_ = 1;
                    v___y_1893_ = v___y_1931_;
                    v___y_1894_ = v___y_1930_;
                    v___y_1895_ = v___y_1933_;
                    v___y_1896_ = v___y_1926_;
                    v___y_1897_ = v___y_1932_;
                    v___y_1898_ = v___x_1946_;
                    v___y_1899_ = v___x_1949_;
                    state = 14;
                    continue;
                } else {
                    v___x_1950_ = 0;
                    v___y_1893_ = v___y_1931_;
                    v___y_1894_ = v___y_1930_;
                    v___y_1895_ = v___y_1933_;
                    v___y_1896_ = v___y_1926_;
                    v___y_1897_ = v___y_1932_;
                    v___y_1898_ = v___x_1946_;
                    v___y_1899_ = v___x_1950_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                if v_isShared_1956_ == 0 {
                    v___x_1958_ = v___x_1955_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
                    v___x_1958_ = v_reuseFailAlloc_1959_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1958_;
            }
            22 => {
                if v_isShared_1964_ == 0 {
                    v___x_1966_ = v___x_1963_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
                    v___x_1966_ = v_reuseFailAlloc_1967_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1966_;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_1984_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_1984_, 1);
                    crate::leanh::lean_inc_ref(v___y_1979_);
                    v___x_1985_ =
                        l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(
                            v___y_1975_,
                            v___y_1979_,
                            v___y_1980_,
                            v___y_1974_,
                            v___y_1976_,
                            v___y_1970_,
                            v___y_1971_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1985_) == 0 {
                        v_a_1986_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                        crate::leanh::lean_inc(v_a_1986_);
                        crate::leanh::lean_dec_ref_known(v___x_1985_, 1);
                        v___x_1987_ = (crate::leanh::lean_unbox(v_a_1986_) as u8);
                        crate::leanh::lean_dec(v_a_1986_);
                        if v___x_1987_ == 0 {
                            v___x_1988_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__8),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_rewrite___lam__1___closed__8_once
                                ),
                                _init_l_Lean_MVarId_rewrite___lam__1___closed__8,
                            );
                            crate::leanh::lean_inc_ref(v___y_1972_);
                            v___x_1989_ = l_Lean_MessageData_ofExpr(v___y_1972_);
                            v___x_1990_ = l_Lean_indentD(v___x_1989_);
                            v___x_1991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_1988_);
                            crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                            v___x_1992_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_rewrite___lam__1___closed__10
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_rewrite___lam__1___closed__10_once
                                ),
                                _init_l_Lean_MVarId_rewrite___lam__1___closed__10,
                            );
                            v___x_1993_ = l_Lean_indentExpr(v___y_1983_);
                            v___x_1994_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1992_);
                            crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                            v___x_1995_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_rewrite___lam__1___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_MVarId_rewrite___lam__1___closed__12_once
                                ),
                                _init_l_Lean_MVarId_rewrite___lam__1___closed__12,
                            );
                            v___x_1996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1994_);
                            crate::leanh::lean_ctor_set(v___x_1996_, 1, v___x_1995_);
                            crate::leanh::lean_inc_ref(v___y_1981_);
                            v___x_1997_ = l_Lean_indentExpr(v___y_1981_);
                            v___x_1998_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1998_, 0, v___x_1996_);
                            crate::leanh::lean_ctor_set(v___x_1998_, 1, v___x_1997_);
                            v___x_1999_ = l_Lean_MessageData_note(v___x_1998_);
                            v___x_2000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2000_, 0, v___x_1991_);
                            crate::leanh::lean_ctor_set(v___x_2000_, 1, v___x_1999_);
                            if v_isShared_1821_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_1820_, 1);
                                crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_2000_);
                                v___x_2002_ = v___x_1820_;
                                state = 25;
                                continue;
                            } else {
                                v_reuseFailAlloc_2012_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2000_);
                                v___x_2002_ = v_reuseFailAlloc_2012_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_1983_);
                            crate::leanh::lean_del_object(v___x_1820_);
                            v___y_1923_ = v___y_1972_;
                            v___y_1924_ = v___y_1973_;
                            v___y_1925_ = v___y_1977_;
                            v___y_1926_ = v___y_1978_;
                            v___y_1927_ = v___y_1979_;
                            v___y_1928_ = v___y_1981_;
                            v___y_1929_ = v___y_1982_;
                            v___y_1930_ = v___y_1974_;
                            v___y_1931_ = v___y_1976_;
                            v___y_1932_ = v___y_1970_;
                            v___y_1933_ = v___y_1971_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1983_);
                        crate::leanh::lean_dec_ref(v___y_1982_);
                        crate::leanh::lean_dec_ref(v___y_1981_);
                        crate::leanh::lean_dec_ref(v___y_1979_);
                        crate::leanh::lean_dec_ref(v___y_1978_);
                        crate::leanh::lean_dec_ref(v___y_1977_);
                        crate::leanh::lean_dec(v___y_1976_);
                        crate::leanh::lean_dec_ref(v___y_1974_);
                        crate::leanh::lean_dec_ref(v___y_1973_);
                        crate::leanh::lean_dec_ref(v___y_1972_);
                        crate::leanh::lean_dec(v___y_1971_);
                        crate::leanh::lean_dec_ref(v___y_1970_);
                        crate::leanh::lean_del_object(v___x_1834_);
                        crate::leanh::lean_dec(v_fst_1831_);
                        crate::leanh::lean_del_object(v___x_1829_);
                        crate::leanh::lean_dec(v_fst_1827_);
                        crate::leanh::lean_del_object(v___x_1820_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        v_a_2013_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                        v_isSharedCheck_2020_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1985_)) as u8;
                        if v_isSharedCheck_2020_ == 0 {
                            v___x_2015_ = v___x_1985_;
                            v_isShared_2016_ = v_isSharedCheck_2020_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2013_);
                            crate::leanh::lean_dec(v___x_1985_);
                            v___x_2015_ = crate::leanh::lean_box(0);
                            v_isShared_2016_ = v_isSharedCheck_2020_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1983_);
                    crate::leanh::lean_dec_ref(v___y_1982_);
                    crate::leanh::lean_dec_ref(v___y_1981_);
                    crate::leanh::lean_dec_ref(v___y_1980_);
                    crate::leanh::lean_dec_ref(v___y_1979_);
                    crate::leanh::lean_dec_ref(v___y_1978_);
                    crate::leanh::lean_dec_ref(v___y_1977_);
                    crate::leanh::lean_dec(v___y_1976_);
                    crate::leanh::lean_dec(v___y_1975_);
                    crate::leanh::lean_dec_ref(v___y_1974_);
                    crate::leanh::lean_dec_ref(v___y_1973_);
                    crate::leanh::lean_dec_ref(v___y_1972_);
                    crate::leanh::lean_dec(v___y_1971_);
                    crate::leanh::lean_dec_ref(v___y_1970_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2021_ = crate::leanh::lean_ctor_get(v___y_1984_, 0);
                    v_isSharedCheck_2028_ = (!crate::leanh::lean_is_exclusive(v___y_1984_)) as u8;
                    if v_isSharedCheck_2028_ == 0 {
                        v___x_2023_ = v___y_1984_;
                        v_isShared_2024_ = v_isSharedCheck_2028_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2021_);
                        crate::leanh::lean_dec(v___y_1984_);
                        v___x_2023_ = crate::leanh::lean_box(0);
                        v_isShared_2024_ = v_isSharedCheck_2028_;
                        state = 30;
                        continue;
                    }
                }
            }
            25 => {
                crate::leanh::lean_inc(v_mvarId_1775_);
                crate::leanh::lean_inc(v___x_1776_);
                v___x_2003_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1776_,
                    v_mvarId_1775_,
                    v___x_2002_,
                    v___y_1974_,
                    v___y_1976_,
                    v___y_1970_,
                    v___y_1971_,
                );
                if crate::leanh::lean_obj_tag(v___x_2003_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2003_, 1);
                    v___y_1923_ = v___y_1972_;
                    v___y_1924_ = v___y_1973_;
                    v___y_1925_ = v___y_1977_;
                    v___y_1926_ = v___y_1978_;
                    v___y_1927_ = v___y_1979_;
                    v___y_1928_ = v___y_1981_;
                    v___y_1929_ = v___y_1982_;
                    v___y_1930_ = v___y_1974_;
                    v___y_1931_ = v___y_1976_;
                    v___y_1932_ = v___y_1970_;
                    v___y_1933_ = v___y_1971_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_1982_);
                    crate::leanh::lean_dec_ref(v___y_1981_);
                    crate::leanh::lean_dec_ref(v___y_1979_);
                    crate::leanh::lean_dec_ref(v___y_1978_);
                    crate::leanh::lean_dec_ref(v___y_1977_);
                    crate::leanh::lean_dec(v___y_1976_);
                    crate::leanh::lean_dec_ref(v___y_1974_);
                    crate::leanh::lean_dec_ref(v___y_1973_);
                    crate::leanh::lean_dec_ref(v___y_1972_);
                    crate::leanh::lean_dec(v___y_1971_);
                    crate::leanh::lean_dec_ref(v___y_1970_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2004_ = crate::leanh::lean_ctor_get(v___x_2003_, 0);
                    v_isSharedCheck_2011_ = (!crate::leanh::lean_is_exclusive(v___x_2003_)) as u8;
                    if v_isSharedCheck_2011_ == 0 {
                        v___x_2006_ = v___x_2003_;
                        v_isShared_2007_ = v_isSharedCheck_2011_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2004_);
                        crate::leanh::lean_dec(v___x_2003_);
                        v___x_2006_ = crate::leanh::lean_box(0);
                        v_isShared_2007_ = v_isSharedCheck_2011_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_2007_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2009_;
            }
            28 => {
                if v_isShared_2016_ == 0 {
                    v___x_2018_ = v___x_2015_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
                    v___x_2018_ = v_reuseFailAlloc_2019_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2018_;
            }
            30 => {
                if v_isShared_2024_ == 0 {
                    v___x_2026_ = v___x_2023_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
                    v___x_2026_ = v_reuseFailAlloc_2027_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2026_;
            }
            32 => {
                if v___y_2046_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2044_);
                    v___x_2047_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__14),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__14_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__14,
                    );
                    crate::leanh::lean_inc_ref(v___y_2030_);
                    v___x_2048_ = l_Lean_MessageData_ofExpr(v___y_2030_);
                    v___x_2049_ = l_Lean_indentD(v___x_2048_);
                    v___x_2050_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2047_);
                    crate::leanh::lean_ctor_set(v___x_2050_, 1, v___x_2049_);
                    v___x_2051_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__16),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__16_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__16,
                    );
                    v___x_2052_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2050_);
                    crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2051_);
                    v___x_2053_ = l_Lean_Exception_toMessageData(v___y_2035_);
                    v___x_2054_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2052_);
                    crate::leanh::lean_ctor_set(v___x_2054_, 1, v___x_2053_);
                    v___x_2055_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__18),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__18_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__18,
                    );
                    v___x_2056_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2054_);
                    crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
                    v___x_2057_ = l_Lean_MVarId_rewrite___lam__1___closed__6;
                    v___x_2058_ = l_Lean_MessageData_ofConstName(v___x_2057_, v___y_2046_);
                    v___x_2059_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2056_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v___x_2058_);
                    v___x_2060_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__20),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__20_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__20,
                    );
                    v___x_2061_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2061_, 0, v___x_2059_);
                    crate::leanh::lean_ctor_set(v___x_2061_, 1, v___x_2060_);
                    v___x_2062_ = l_Lean_MVarId_rewrite___lam__1___closed__23;
                    v___x_2063_ = l_Lean_MessageData_ofConstName(v___x_2062_, v___y_2046_);
                    v___x_2064_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2061_);
                    crate::leanh::lean_ctor_set(v___x_2064_, 1, v___x_2063_);
                    v___x_2065_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__25),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__25_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__25,
                    );
                    v___x_2066_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                    crate::leanh::lean_ctor_set(v___x_2066_, 1, v___x_2065_);
                    v___x_2067_ = l_Lean_MVarId_rewrite___lam__1___closed__27;
                    v___x_2068_ = l_Lean_MessageData_ofConstName(v___x_2067_, v___y_2046_);
                    v___x_2069_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2069_, 0, v___x_2066_);
                    crate::leanh::lean_ctor_set(v___x_2069_, 1, v___x_2068_);
                    v___x_2070_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__29),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__29_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__29,
                    );
                    v___x_2071_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2071_, 0, v___x_2069_);
                    crate::leanh::lean_ctor_set(v___x_2071_, 1, v___x_2070_);
                    v___x_2072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                    crate::leanh::lean_inc(v_mvarId_1775_);
                    crate::leanh::lean_inc(v___x_1776_);
                    v___x_2073_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_1776_,
                        v_mvarId_1775_,
                        v___x_2072_,
                        v___y_2034_,
                        v___y_2037_,
                        v___y_2031_,
                        v___y_2032_,
                    );
                    v___y_1970_ = v___y_2031_;
                    v___y_1971_ = v___y_2032_;
                    v___y_1972_ = v___y_2030_;
                    v___y_1973_ = v___y_2033_;
                    v___y_1974_ = v___y_2034_;
                    v___y_1975_ = v___y_2036_;
                    v___y_1976_ = v___y_2037_;
                    v___y_1977_ = v___y_2038_;
                    v___y_1978_ = v___y_2039_;
                    v___y_1979_ = v___y_2040_;
                    v___y_1980_ = v___y_2041_;
                    v___y_1981_ = v___y_2042_;
                    v___y_1982_ = v___y_2043_;
                    v___y_1983_ = v___y_2045_;
                    v___y_1984_ = v___x_2073_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2035_);
                    v___y_1970_ = v___y_2031_;
                    v___y_1971_ = v___y_2032_;
                    v___y_1972_ = v___y_2030_;
                    v___y_1973_ = v___y_2033_;
                    v___y_1974_ = v___y_2034_;
                    v___y_1975_ = v___y_2036_;
                    v___y_1976_ = v___y_2037_;
                    v___y_1977_ = v___y_2038_;
                    v___y_1978_ = v___y_2039_;
                    v___y_1979_ = v___y_2040_;
                    v___y_1980_ = v___y_2041_;
                    v___y_1981_ = v___y_2042_;
                    v___y_1982_ = v___y_2043_;
                    v___y_1983_ = v___y_2045_;
                    v___y_1984_ = v___y_2044_;
                    state = 24;
                    continue;
                }
            }
            33 => {
                crate::leanh::lean_inc(v___y_2086_);
                crate::leanh::lean_inc_ref(v___y_2085_);
                crate::leanh::lean_inc(v___y_2084_);
                crate::leanh::lean_inc_ref(v___y_2083_);
                crate::leanh::lean_inc_ref(v___y_2081_);
                v___x_2087_ = lean_infer_type(
                    v___y_2081_,
                    v___y_2083_,
                    v___y_2084_,
                    v___y_2085_,
                    v___y_2086_,
                );
                if crate::leanh::lean_obj_tag(v___x_2087_) == 0 {
                    v_a_2088_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                    crate::leanh::lean_inc_n(v_a_2088_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2087_, 1);
                    v___f_2089_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_rewrite___lam__0___boxed as *mut core::ffi::c_void,
                        8,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_2089_, 0, v___y_2075_);
                    crate::leanh::lean_closure_set(v___f_2089_, 1, v_a_2088_);
                    v___x_2090_ = l_Lean_MVarId_rewrite___lam__1___closed__31;
                    v___x_2091_ = 0;
                    crate::leanh::lean_inc_ref(v___y_2079_);
                    v___x_2092_ =
                        l_Lean_mkLambda(v___x_2090_, v___x_2091_, v___y_2079_, v___y_2078_);
                    v___x_2093_ = 0;
                    crate::leanh::lean_inc_ref(v___x_2092_);
                    v___x_2094_ = l_Lean_Meta_check(
                        v___x_2092_,
                        v___x_2093_,
                        v___y_2083_,
                        v___y_2084_,
                        v___y_2085_,
                        v___y_2086_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2094_) == 0 {
                        v___y_1970_ = v___y_2085_;
                        v___y_1971_ = v___y_2086_;
                        v___y_1972_ = v___x_2092_;
                        v___y_1973_ = v___y_2076_;
                        v___y_1974_ = v___y_2083_;
                        v___y_1975_ = v___x_2090_;
                        v___y_1976_ = v___y_2084_;
                        v___y_1977_ = v___y_2077_;
                        v___y_1978_ = v_eNew_2082_;
                        v___y_1979_ = v___y_2079_;
                        v___y_1980_ = v___f_2089_;
                        v___y_1981_ = v___y_2080_;
                        v___y_1982_ = v_a_2088_;
                        v___y_1983_ = v___y_2081_;
                        v___y_1984_ = v___x_2094_;
                        state = 24;
                        continue;
                    } else {
                        v_a_2095_ = crate::leanh::lean_ctor_get(v___x_2094_, 0);
                        crate::leanh::lean_inc(v_a_2095_);
                        v___x_2096_ = l_Lean_Exception_isInterrupt(v_a_2095_);
                        if v___x_2096_ == 0 {
                            crate::leanh::lean_inc(v_a_2095_);
                            v___x_2097_ = l_Lean_Exception_isRuntime(v_a_2095_);
                            v___y_2030_ = v___x_2092_;
                            v___y_2031_ = v___y_2085_;
                            v___y_2032_ = v___y_2086_;
                            v___y_2033_ = v___y_2076_;
                            v___y_2034_ = v___y_2083_;
                            v___y_2035_ = v_a_2095_;
                            v___y_2036_ = v___x_2090_;
                            v___y_2037_ = v___y_2084_;
                            v___y_2038_ = v___y_2077_;
                            v___y_2039_ = v_eNew_2082_;
                            v___y_2040_ = v___y_2079_;
                            v___y_2041_ = v___f_2089_;
                            v___y_2042_ = v___y_2080_;
                            v___y_2043_ = v_a_2088_;
                            v___y_2044_ = v___x_2094_;
                            v___y_2045_ = v___y_2081_;
                            v___y_2046_ = v___x_2097_;
                            state = 32;
                            continue;
                        } else {
                            v___y_2030_ = v___x_2092_;
                            v___y_2031_ = v___y_2085_;
                            v___y_2032_ = v___y_2086_;
                            v___y_2033_ = v___y_2076_;
                            v___y_2034_ = v___y_2083_;
                            v___y_2035_ = v_a_2095_;
                            v___y_2036_ = v___x_2090_;
                            v___y_2037_ = v___y_2084_;
                            v___y_2038_ = v___y_2077_;
                            v___y_2039_ = v_eNew_2082_;
                            v___y_2040_ = v___y_2079_;
                            v___y_2041_ = v___f_2089_;
                            v___y_2042_ = v___y_2080_;
                            v___y_2043_ = v_a_2088_;
                            v___y_2044_ = v___x_2094_;
                            v___y_2045_ = v___y_2081_;
                            v___y_2046_ = v___x_2096_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2086_);
                    crate::leanh::lean_dec_ref(v___y_2085_);
                    crate::leanh::lean_dec(v___y_2084_);
                    crate::leanh::lean_dec_ref(v___y_2083_);
                    crate::leanh::lean_dec_ref(v_eNew_2082_);
                    crate::leanh::lean_dec_ref(v___y_2081_);
                    crate::leanh::lean_dec_ref(v___y_2080_);
                    crate::leanh::lean_dec_ref(v___y_2079_);
                    crate::leanh::lean_dec_ref(v___y_2078_);
                    crate::leanh::lean_dec_ref(v___y_2077_);
                    crate::leanh::lean_dec_ref(v___y_2076_);
                    crate::leanh::lean_dec_ref(v___y_2075_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2098_ = crate::leanh::lean_ctor_get(v___x_2087_, 0);
                    v_isSharedCheck_2105_ = (!crate::leanh::lean_is_exclusive(v___x_2087_)) as u8;
                    if v_isSharedCheck_2105_ == 0 {
                        v___x_2100_ = v___x_2087_;
                        v_isShared_2101_ = v_isSharedCheck_2105_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2098_);
                        crate::leanh::lean_dec(v___x_2087_);
                        v___x_2100_ = crate::leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2105_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2101_ == 0 {
                    v___x_2103_ = v___x_2100_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2103_;
            }
            36 => {
                v___x_2117_ = lean_expr_instantiate1(v___y_2107_, v___y_2108_);
                v___x_2118_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
                    v___x_2117_,
                    v___y_2114_,
                );
                v_a_2119_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                crate::leanh::lean_inc(v_a_2119_);
                crate::leanh::lean_dec_ref(v___x_2118_);
                v___x_2120_ = l_Lean_Expr_hasBinderNameHint(v___y_2108_);
                if v___x_2120_ == 0 {
                    crate::leanh::lean_inc_ref(v___y_2107_);
                    v___y_2075_ = v___y_2107_;
                    v___y_2076_ = v___y_2108_;
                    v___y_2077_ = v___y_2109_;
                    v___y_2078_ = v___y_2107_;
                    v___y_2079_ = v___y_2110_;
                    v___y_2080_ = v___y_2111_;
                    v___y_2081_ = v___y_2112_;
                    v_eNew_2082_ = v_a_2119_;
                    v___y_2083_ = v___y_2113_;
                    v___y_2084_ = v___y_2114_;
                    v___y_2085_ = v___y_2115_;
                    v___y_2086_ = v___y_2116_;
                    state = 33;
                    continue;
                } else {
                    v___x_2121_ =
                        l_Lean_Expr_resolveBinderNameHint(v_a_2119_, v___y_2115_, v___y_2116_);
                    if crate::leanh::lean_obj_tag(v___x_2121_) == 0 {
                        v_a_2122_ = crate::leanh::lean_ctor_get(v___x_2121_, 0);
                        crate::leanh::lean_inc(v_a_2122_);
                        crate::leanh::lean_dec_ref_known(v___x_2121_, 1);
                        crate::leanh::lean_inc_ref(v___y_2107_);
                        v___y_2075_ = v___y_2107_;
                        v___y_2076_ = v___y_2108_;
                        v___y_2077_ = v___y_2109_;
                        v___y_2078_ = v___y_2107_;
                        v___y_2079_ = v___y_2110_;
                        v___y_2080_ = v___y_2111_;
                        v___y_2081_ = v___y_2112_;
                        v_eNew_2082_ = v_a_2122_;
                        v___y_2083_ = v___y_2113_;
                        v___y_2084_ = v___y_2114_;
                        v___y_2085_ = v___y_2115_;
                        v___y_2086_ = v___y_2116_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2116_);
                        crate::leanh::lean_dec_ref(v___y_2115_);
                        crate::leanh::lean_dec(v___y_2114_);
                        crate::leanh::lean_dec_ref(v___y_2113_);
                        crate::leanh::lean_dec_ref(v___y_2112_);
                        crate::leanh::lean_dec_ref(v___y_2111_);
                        crate::leanh::lean_dec_ref(v___y_2110_);
                        crate::leanh::lean_dec_ref(v___y_2109_);
                        crate::leanh::lean_dec_ref(v___y_2108_);
                        crate::leanh::lean_dec_ref(v___y_2107_);
                        crate::leanh::lean_del_object(v___x_1834_);
                        crate::leanh::lean_dec(v_fst_1831_);
                        crate::leanh::lean_del_object(v___x_1829_);
                        crate::leanh::lean_dec(v_fst_1827_);
                        crate::leanh::lean_del_object(v___x_1820_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        v_a_2123_ = crate::leanh::lean_ctor_get(v___x_2121_, 0);
                        v_isSharedCheck_2130_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2121_)) as u8;
                        if v_isSharedCheck_2130_ == 0 {
                            v___x_2125_ = v___x_2121_;
                            v_isShared_2126_ = v_isSharedCheck_2130_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2123_);
                            crate::leanh::lean_dec(v___x_2121_);
                            v___x_2125_ = crate::leanh::lean_box(0);
                            v_isShared_2126_ = v_isSharedCheck_2130_;
                            state = 37;
                            continue;
                        }
                    }
                }
            }
            37 => {
                if v_isShared_2126_ == 0 {
                    v___x_2128_ = v___x_2125_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2128_;
            }
            39 => {
                v___x_2140_ = l_Lean_instantiateMVars___at___00Lean_MVarId_rewrite_spec__1___redArg(
                    v_e_1778_,
                    v___y_2137_,
                );
                v_a_2141_ = crate::leanh::lean_ctor_get(v___x_2140_, 0);
                v_isSharedCheck_2234_ = (!crate::leanh::lean_is_exclusive(v___x_2140_)) as u8;
                if v_isSharedCheck_2234_ == 0 {
                    v___x_2143_ = v___x_2140_;
                    v_isShared_2144_ = v_isSharedCheck_2234_;
                    state = 40;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2141_);
                    crate::leanh::lean_dec(v___x_2140_);
                    v___x_2143_ = crate::leanh::lean_box(0);
                    v_isShared_2144_ = v_isSharedCheck_2234_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v_transparency_2145_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1779_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_offsetCnstrs_2146_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1779_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_occs_2147_ = crate::leanh::lean_ctor_get(v_config_1779_, 0);
                crate::leanh::lean_inc(v_occs_2147_);
                crate::leanh::lean_dec_ref(v_config_1779_);
                v___x_2148_ = l_Lean_Meta_Context_config(v___y_2136_);
                v_foApprox_2149_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 0 as u32);
                v_ctxApprox_2150_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 1 as u32);
                v_quasiPatternApprox_2151_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2148_, 2 as u32);
                v_constApprox_2152_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 3 as u32);
                v_isDefEqStuckEx_2153_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 4 as u32);
                v_unificationHints_2154_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 5 as u32);
                v_proofIrrelevance_2155_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 6 as u32);
                v_assignSyntheticOpaque_2156_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2148_, 7 as u32);
                v_etaStruct_2157_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 10 as u32);
                v_univApprox_2158_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 11 as u32);
                v_iota_2159_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 12 as u32);
                v_beta_2160_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 13 as u32);
                v_proj_2161_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 14 as u32);
                v_zeta_2162_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 15 as u32);
                v_zetaDelta_2163_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 16 as u32);
                v_zetaUnused_2164_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 17 as u32);
                v_zetaHave_2165_ = crate::leanh::lean_ctor_get_uint8(v___x_2148_, 18 as u32);
                v_isSharedCheck_2233_ = (!crate::leanh::lean_is_exclusive(v___x_2148_)) as u8;
                if v_isSharedCheck_2233_ == 0 {
                    v___x_2167_ = v___x_2148_;
                    v_isShared_2168_ = v_isSharedCheck_2233_;
                    state = 41;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2148_);
                    v___x_2167_ = crate::leanh::lean_box(0);
                    v_isShared_2168_ = v_isSharedCheck_2233_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v_trackZetaDelta_2169_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2136_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2170_ = crate::leanh::lean_ctor_get(v___y_2136_, 1);
                v_lctx_2171_ = crate::leanh::lean_ctor_get(v___y_2136_, 2);
                v_localInstances_2172_ = crate::leanh::lean_ctor_get(v___y_2136_, 3);
                v_defEqCtx_x3f_2173_ = crate::leanh::lean_ctor_get(v___y_2136_, 4);
                v_synthPendingDepth_2174_ = crate::leanh::lean_ctor_get(v___y_2136_, 5);
                v_canUnfold_x3f_2175_ = crate::leanh::lean_ctor_get(v___y_2136_, 6);
                v_univApprox_2176_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2136_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2177_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2136_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2178_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2136_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2168_ == 0 {
                    v___x_2180_ = v___x_2167_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        0 as u32,
                        v_foApprox_2149_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        1 as u32,
                        v_ctxApprox_2150_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        2 as u32,
                        v_quasiPatternApprox_2151_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        3 as u32,
                        v_constApprox_2152_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        4 as u32,
                        v_isDefEqStuckEx_2153_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        5 as u32,
                        v_unificationHints_2154_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        6 as u32,
                        v_proofIrrelevance_2155_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        7 as u32,
                        v_assignSyntheticOpaque_2156_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        10 as u32,
                        v_etaStruct_2157_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        11 as u32,
                        v_univApprox_2158_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        12 as u32,
                        v_iota_2159_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        13 as u32,
                        v_beta_2160_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        14 as u32,
                        v_proj_2161_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        15 as u32,
                        v_zeta_2162_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        16 as u32,
                        v_zetaDelta_2163_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        17 as u32,
                        v_zetaUnused_2164_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2232_,
                        18 as u32,
                        v_zetaHave_2165_,
                    );
                    v___x_2180_ = v_reuseFailAlloc_2232_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                crate::leanh::lean_ctor_set_uint8(v___x_2180_, 8 as u32, v_offsetCnstrs_2146_);
                crate::leanh::lean_ctor_set_uint8(v___x_2180_, 9 as u32, v_transparency_2145_);
                v___x_2181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2180_);
                v___x_2182_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2182_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2182_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2181_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2175_);
                crate::leanh::lean_inc(v_synthPendingDepth_2174_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2173_);
                crate::leanh::lean_inc_ref(v_localInstances_2172_);
                crate::leanh::lean_inc_ref(v_lctx_2171_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2170_);
                v___x_2183_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2182_);
                crate::leanh::lean_ctor_set(v___x_2183_, 1, v_zetaDeltaSet_2170_);
                crate::leanh::lean_ctor_set(v___x_2183_, 2, v_lctx_2171_);
                crate::leanh::lean_ctor_set(v___x_2183_, 3, v_localInstances_2172_);
                crate::leanh::lean_ctor_set(v___x_2183_, 4, v_defEqCtx_x3f_2173_);
                crate::leanh::lean_ctor_set(v___x_2183_, 5, v_synthPendingDepth_2174_);
                crate::leanh::lean_ctor_set(v___x_2183_, 6, v_canUnfold_x3f_2175_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2169_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2176_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2177_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2183_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2178_,
                );
                crate::leanh::lean_inc_ref(v___y_2135_);
                crate::leanh::lean_inc(v_a_2141_);
                v___x_2184_ = l_Lean_Meta_kabstract(
                    v_a_2141_,
                    v___y_2135_,
                    v_occs_2147_,
                    v___x_2183_,
                    v___y_2137_,
                    v___y_2138_,
                    v___y_2139_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2183_, 7);
                if crate::leanh::lean_obj_tag(v___x_2184_) == 0 {
                    v_a_2185_ = crate::leanh::lean_ctor_get(v___x_2184_, 0);
                    crate::leanh::lean_inc(v_a_2185_);
                    crate::leanh::lean_dec_ref_known(v___x_2184_, 1);
                    v___x_2186_ = l_Lean_Expr_hasLooseBVars(v_a_2185_);
                    if v___x_2186_ == 0 {
                        crate::leanh::lean_inc_ref(v___y_2135_);
                        crate::leanh::lean_inc(v_a_2141_);
                        v___x_2187_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                            v_a_2141_,
                            v___y_2135_,
                            v___y_2136_,
                            v___y_2137_,
                            v___y_2138_,
                            v___y_2139_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2187_) == 0 {
                            v_a_2188_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                            crate::leanh::lean_inc(v_a_2188_);
                            crate::leanh::lean_dec_ref_known(v___x_2187_, 1);
                            v_fst_2189_ = crate::leanh::lean_ctor_get(v_a_2188_, 0);
                            v_snd_2190_ = crate::leanh::lean_ctor_get(v_a_2188_, 1);
                            v_isSharedCheck_2215_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2188_)) as u8;
                            if v_isSharedCheck_2215_ == 0 {
                                v___x_2192_ = v_a_2188_;
                                v_isShared_2193_ = v_isSharedCheck_2215_;
                                state = 43;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2190_);
                                crate::leanh::lean_inc(v_fst_2189_);
                                crate::leanh::lean_dec(v_a_2188_);
                                v___x_2192_ = crate::leanh::lean_box(0);
                                v_isShared_2193_ = v_isSharedCheck_2215_;
                                state = 43;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2185_);
                            crate::leanh::lean_del_object(v___x_2143_);
                            crate::leanh::lean_dec(v_a_2141_);
                            crate::leanh::lean_dec(v___y_2139_);
                            crate::leanh::lean_dec_ref(v___y_2138_);
                            crate::leanh::lean_dec(v___y_2137_);
                            crate::leanh::lean_dec_ref(v___y_2136_);
                            crate::leanh::lean_dec_ref(v___y_2135_);
                            crate::leanh::lean_dec_ref(v___y_2134_);
                            crate::leanh::lean_dec_ref(v___y_2133_);
                            crate::leanh::lean_dec_ref(v___y_2132_);
                            crate::leanh::lean_del_object(v___x_1834_);
                            crate::leanh::lean_dec(v_fst_1831_);
                            crate::leanh::lean_del_object(v___x_1829_);
                            crate::leanh::lean_dec(v_fst_1827_);
                            crate::leanh::lean_del_object(v___x_1820_);
                            crate::leanh::lean_dec_ref(v_heq_1777_);
                            crate::leanh::lean_dec(v___x_1776_);
                            crate::leanh::lean_dec(v_mvarId_1775_);
                            v_a_2216_ = crate::leanh::lean_ctor_get(v___x_2187_, 0);
                            v_isSharedCheck_2223_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2187_)) as u8;
                            if v_isSharedCheck_2223_ == 0 {
                                v___x_2218_ = v___x_2187_;
                                v_isShared_2219_ = v_isSharedCheck_2223_;
                                state = 48;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2216_);
                                crate::leanh::lean_dec(v___x_2187_);
                                v___x_2218_ = crate::leanh::lean_box(0);
                                v_isShared_2219_ = v_isSharedCheck_2223_;
                                state = 48;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2143_);
                        v___y_2107_ = v_a_2185_;
                        v___y_2108_ = v___y_2132_;
                        v___y_2109_ = v___y_2133_;
                        v___y_2110_ = v___y_2134_;
                        v___y_2111_ = v___y_2135_;
                        v___y_2112_ = v_a_2141_;
                        v___y_2113_ = v___y_2136_;
                        v___y_2114_ = v___y_2137_;
                        v___y_2115_ = v___y_2138_;
                        v___y_2116_ = v___y_2139_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2143_);
                    crate::leanh::lean_dec(v_a_2141_);
                    crate::leanh::lean_dec(v___y_2139_);
                    crate::leanh::lean_dec_ref(v___y_2138_);
                    crate::leanh::lean_dec(v___y_2137_);
                    crate::leanh::lean_dec_ref(v___y_2136_);
                    crate::leanh::lean_dec_ref(v___y_2135_);
                    crate::leanh::lean_dec_ref(v___y_2134_);
                    crate::leanh::lean_dec_ref(v___y_2133_);
                    crate::leanh::lean_dec_ref(v___y_2132_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2224_ = crate::leanh::lean_ctor_get(v___x_2184_, 0);
                    v_isSharedCheck_2231_ = (!crate::leanh::lean_is_exclusive(v___x_2184_)) as u8;
                    if v_isSharedCheck_2231_ == 0 {
                        v___x_2226_ = v___x_2184_;
                        v_isShared_2227_ = v_isSharedCheck_2231_;
                        state = 50;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2224_);
                        crate::leanh::lean_dec(v___x_2184_);
                        v___x_2226_ = crate::leanh::lean_box(0);
                        v_isShared_2227_ = v_isSharedCheck_2231_;
                        state = 50;
                        continue;
                    }
                }
            }
            43 => {
                v___x_2194_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__33),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__33_once),
                    _init_l_Lean_MVarId_rewrite___lam__1___closed__33,
                );
                v___x_2195_ = l_Lean_indentExpr(v_snd_2190_);
                if v_isShared_2193_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2192_, 7);
                    crate::leanh::lean_ctor_set(v___x_2192_, 1, v___x_2195_);
                    crate::leanh::lean_ctor_set(v___x_2192_, 0, v___x_2194_);
                    v___x_2197_ = v___x_2192_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2195_);
                    v___x_2197_ = v_reuseFailAlloc_2214_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_2198_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__35),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__35_once),
                    _init_l_Lean_MVarId_rewrite___lam__1___closed__35,
                );
                v___x_2199_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2197_);
                crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2198_);
                v___x_2200_ = l_Lean_indentExpr(v_fst_2189_);
                v___x_2201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2199_);
                crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2143_, 1);
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2201_);
                    v___x_2203_ = v___x_2143_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2201_);
                    v___x_2203_ = v_reuseFailAlloc_2213_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                crate::leanh::lean_inc(v_mvarId_1775_);
                crate::leanh::lean_inc(v___x_1776_);
                v___x_2204_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_1776_,
                    v_mvarId_1775_,
                    v___x_2203_,
                    v___y_2136_,
                    v___y_2137_,
                    v___y_2138_,
                    v___y_2139_,
                );
                if crate::leanh::lean_obj_tag(v___x_2204_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2204_, 1);
                    v___y_2107_ = v_a_2185_;
                    v___y_2108_ = v___y_2132_;
                    v___y_2109_ = v___y_2133_;
                    v___y_2110_ = v___y_2134_;
                    v___y_2111_ = v___y_2135_;
                    v___y_2112_ = v_a_2141_;
                    v___y_2113_ = v___y_2136_;
                    v___y_2114_ = v___y_2137_;
                    v___y_2115_ = v___y_2138_;
                    v___y_2116_ = v___y_2139_;
                    state = 36;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2185_);
                    crate::leanh::lean_dec(v_a_2141_);
                    crate::leanh::lean_dec(v___y_2139_);
                    crate::leanh::lean_dec_ref(v___y_2138_);
                    crate::leanh::lean_dec(v___y_2137_);
                    crate::leanh::lean_dec_ref(v___y_2136_);
                    crate::leanh::lean_dec_ref(v___y_2135_);
                    crate::leanh::lean_dec_ref(v___y_2134_);
                    crate::leanh::lean_dec_ref(v___y_2133_);
                    crate::leanh::lean_dec_ref(v___y_2132_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2205_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                    v_isSharedCheck_2212_ = (!crate::leanh::lean_is_exclusive(v___x_2204_)) as u8;
                    if v_isSharedCheck_2212_ == 0 {
                        v___x_2207_ = v___x_2204_;
                        v_isShared_2208_ = v_isSharedCheck_2212_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2205_);
                        crate::leanh::lean_dec(v___x_2204_);
                        v___x_2207_ = crate::leanh::lean_box(0);
                        v_isShared_2208_ = v_isSharedCheck_2212_;
                        state = 46;
                        continue;
                    }
                }
            }
            46 => {
                if v_isShared_2208_ == 0 {
                    v___x_2210_ = v___x_2207_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
                    v___x_2210_ = v_reuseFailAlloc_2211_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2210_;
            }
            48 => {
                if v_isShared_2219_ == 0 {
                    v___x_2221_ = v___x_2218_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2222_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_2221_;
            }
            50 => {
                if v_isShared_2227_ == 0 {
                    v___x_2229_ = v___x_2226_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
                    v___x_2229_ = v_reuseFailAlloc_2230_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_2229_;
            }
            52 => {
                v___x_2245_ = l_Lean_Expr_getAppFn(v_lhs_2239_);
                v___x_2246_ = l_Lean_Expr_isMVar(v___x_2245_);
                crate::leanh::lean_dec_ref(v___x_2245_);
                if v___x_2246_ == 0 {
                    crate::leanh::lean_dec_ref(v_heqType_2238_);
                    v___y_2132_ = v_rhs_2240_;
                    v___y_2133_ = v_heq_2237_;
                    v___y_2134_ = v___y_2236_;
                    v___y_2135_ = v_lhs_2239_;
                    v___y_2136_ = v___y_2241_;
                    v___y_2137_ = v___y_2242_;
                    v___y_2138_ = v___y_2243_;
                    v___y_2139_ = v___y_2244_;
                    state = 39;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_2240_);
                    crate::leanh::lean_dec_ref(v_heq_2237_);
                    crate::leanh::lean_dec_ref(v___y_2236_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_config_1779_);
                    crate::leanh::lean_dec_ref(v_e_1778_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v___x_2247_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__37),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__37_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__37,
                    );
                    v___x_2248_ = l_Lean_MessageData_ofExpr(v_lhs_2239_);
                    v___x_2249_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2249_, 0, v___x_2247_);
                    crate::leanh::lean_ctor_set(v___x_2249_, 1, v___x_2248_);
                    v___x_2250_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__39),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_rewrite___lam__1___closed__39_once),
                        _init_l_Lean_MVarId_rewrite___lam__1___closed__39,
                    );
                    v___x_2251_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2249_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
                    v___x_2252_ = l_Lean_indentExpr(v_heqType_2238_);
                    v___x_2253_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2251_);
                    crate::leanh::lean_ctor_set(v___x_2253_, 1, v___x_2252_);
                    v___x_2254_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(
                        v___x_2253_,
                        v___y_2241_,
                        v___y_2242_,
                        v___y_2243_,
                        v___y_2244_,
                    );
                    crate::leanh::lean_dec(v___y_2244_);
                    crate::leanh::lean_dec_ref(v___y_2243_);
                    crate::leanh::lean_dec(v___y_2242_);
                    crate::leanh::lean_dec_ref(v___y_2241_);
                    v_a_2255_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                    v_isSharedCheck_2262_ = (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2257_ = v___x_2254_;
                        v_isShared_2258_ = v_isSharedCheck_2262_;
                        state = 53;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2255_);
                        crate::leanh::lean_dec(v___x_2254_);
                        v___x_2257_ = crate::leanh::lean_box(0);
                        v_isShared_2258_ = v_isSharedCheck_2262_;
                        state = 53;
                        continue;
                    }
                }
            }
            53 => {
                if v_isShared_2258_ == 0 {
                    v___x_2260_ = v___x_2257_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2260_;
            }
            55 => {
                crate::leanh::lean_inc_ref(v_heqType_2265_);
                v___x_2270_ = l_Lean_Meta_matchEq_x3f(
                    v_heqType_2265_,
                    v___y_2266_,
                    v___y_2267_,
                    v___y_2268_,
                    v___y_2269_,
                );
                if crate::leanh::lean_obj_tag(v___x_2270_) == 0 {
                    v_a_2271_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                    crate::leanh::lean_inc(v_a_2271_);
                    crate::leanh::lean_dec_ref_known(v___x_2270_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2271_) == 0 {
                        crate::leanh::lean_del_object(v___x_1834_);
                        crate::leanh::lean_dec(v_fst_1831_);
                        crate::leanh::lean_del_object(v___x_1829_);
                        crate::leanh::lean_dec(v_fst_1827_);
                        crate::leanh::lean_del_object(v___x_1820_);
                        crate::leanh::lean_dec_ref(v_config_1779_);
                        crate::leanh::lean_dec_ref(v_e_1778_);
                        crate::leanh::lean_dec_ref(v_heq_1777_);
                        crate::leanh::lean_dec(v___x_1776_);
                        crate::leanh::lean_dec(v_mvarId_1775_);
                        crate::leanh::lean_inc_ref(v_heqType_2265_);
                        v___x_2272_ = l_Lean_Meta_isProp(
                            v_heqType_2265_,
                            v___y_2266_,
                            v___y_2267_,
                            v___y_2268_,
                            v___y_2269_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2272_) == 0 {
                            v_a_2273_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                            crate::leanh::lean_inc(v_a_2273_);
                            crate::leanh::lean_dec_ref_known(v___x_2272_, 1);
                            v___x_2274_ = (crate::leanh::lean_unbox(v_a_2273_) as u8);
                            crate::leanh::lean_dec(v_a_2273_);
                            if v___x_2274_ == 0 {
                                v___x_2275_ = l_Lean_MVarId_rewrite___lam__1___closed__40;
                                v___y_1787_ = v___y_2269_;
                                v___y_1788_ = v___y_2268_;
                                v___y_1789_ = v_heqType_2265_;
                                v___y_1790_ = v___y_2267_;
                                v___y_1791_ = v___y_2266_;
                                v___y_1792_ = v_heq_2264_;
                                v___y_1793_ = v___x_2275_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2276_ = l_Lean_MVarId_rewrite___lam__1___closed__41;
                                v___y_1787_ = v___y_2269_;
                                v___y_1788_ = v___y_2268_;
                                v___y_1789_ = v_heqType_2265_;
                                v___y_1790_ = v___y_2267_;
                                v___y_1791_ = v___y_2266_;
                                v___y_1792_ = v_heq_2264_;
                                v___y_1793_ = v___x_2276_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_2269_);
                            crate::leanh::lean_dec_ref(v___y_2268_);
                            crate::leanh::lean_dec(v___y_2267_);
                            crate::leanh::lean_dec_ref(v___y_2266_);
                            crate::leanh::lean_dec_ref(v_heqType_2265_);
                            crate::leanh::lean_dec_ref(v_heq_2264_);
                            v_a_2277_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                            v_isSharedCheck_2284_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2272_)) as u8;
                            if v_isSharedCheck_2284_ == 0 {
                                v___x_2279_ = v___x_2272_;
                                v_isShared_2280_ = v_isSharedCheck_2284_;
                                state = 56;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2277_);
                                crate::leanh::lean_dec(v___x_2272_);
                                v___x_2279_ = crate::leanh::lean_box(0);
                                v_isShared_2280_ = v_isSharedCheck_2284_;
                                state = 56;
                                continue;
                            }
                        }
                    } else {
                        v_val_2285_ = crate::leanh::lean_ctor_get(v_a_2271_, 0);
                        crate::leanh::lean_inc(v_val_2285_);
                        crate::leanh::lean_dec_ref_known(v_a_2271_, 1);
                        v_snd_2286_ = crate::leanh::lean_ctor_get(v_val_2285_, 1);
                        crate::leanh::lean_inc(v_snd_2286_);
                        if v_symm_1780_ == 0 {
                            v_fst_2287_ = crate::leanh::lean_ctor_get(v_val_2285_, 0);
                            crate::leanh::lean_inc(v_fst_2287_);
                            crate::leanh::lean_dec(v_val_2285_);
                            v_fst_2288_ = crate::leanh::lean_ctor_get(v_snd_2286_, 0);
                            crate::leanh::lean_inc(v_fst_2288_);
                            v_snd_2289_ = crate::leanh::lean_ctor_get(v_snd_2286_, 1);
                            crate::leanh::lean_inc(v_snd_2289_);
                            crate::leanh::lean_dec(v_snd_2286_);
                            v___y_2236_ = v_fst_2287_;
                            v_heq_2237_ = v_heq_2264_;
                            v_heqType_2238_ = v_heqType_2265_;
                            v_lhs_2239_ = v_fst_2288_;
                            v_rhs_2240_ = v_snd_2289_;
                            v___y_2241_ = v___y_2266_;
                            v___y_2242_ = v___y_2267_;
                            v___y_2243_ = v___y_2268_;
                            v___y_2244_ = v___y_2269_;
                            state = 52;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_heqType_2265_);
                            v_fst_2290_ = crate::leanh::lean_ctor_get(v_val_2285_, 0);
                            crate::leanh::lean_inc(v_fst_2290_);
                            crate::leanh::lean_dec(v_val_2285_);
                            v_fst_2291_ = crate::leanh::lean_ctor_get(v_snd_2286_, 0);
                            crate::leanh::lean_inc(v_fst_2291_);
                            v_snd_2292_ = crate::leanh::lean_ctor_get(v_snd_2286_, 1);
                            crate::leanh::lean_inc(v_snd_2292_);
                            crate::leanh::lean_dec(v_snd_2286_);
                            v___x_2293_ = l_Lean_Meta_mkEqSymm(
                                v_heq_2264_,
                                v___y_2266_,
                                v___y_2267_,
                                v___y_2268_,
                                v___y_2269_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2293_) == 0 {
                                v_a_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                                crate::leanh::lean_inc(v_a_2294_);
                                crate::leanh::lean_dec_ref_known(v___x_2293_, 1);
                                crate::leanh::lean_inc(v_fst_2291_);
                                crate::leanh::lean_inc(v_snd_2292_);
                                v___x_2295_ = l_Lean_Meta_mkEq(
                                    v_snd_2292_,
                                    v_fst_2291_,
                                    v___y_2266_,
                                    v___y_2267_,
                                    v___y_2268_,
                                    v___y_2269_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2295_) == 0 {
                                    v_a_2296_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                                    crate::leanh::lean_inc(v_a_2296_);
                                    crate::leanh::lean_dec_ref_known(v___x_2295_, 1);
                                    v___y_2236_ = v_fst_2290_;
                                    v_heq_2237_ = v_a_2294_;
                                    v_heqType_2238_ = v_a_2296_;
                                    v_lhs_2239_ = v_snd_2292_;
                                    v_rhs_2240_ = v_fst_2291_;
                                    v___y_2241_ = v___y_2266_;
                                    v___y_2242_ = v___y_2267_;
                                    v___y_2243_ = v___y_2268_;
                                    v___y_2244_ = v___y_2269_;
                                    state = 52;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_2294_);
                                    crate::leanh::lean_dec(v_snd_2292_);
                                    crate::leanh::lean_dec(v_fst_2291_);
                                    crate::leanh::lean_dec(v_fst_2290_);
                                    crate::leanh::lean_dec(v___y_2269_);
                                    crate::leanh::lean_dec_ref(v___y_2268_);
                                    crate::leanh::lean_dec(v___y_2267_);
                                    crate::leanh::lean_dec_ref(v___y_2266_);
                                    crate::leanh::lean_del_object(v___x_1834_);
                                    crate::leanh::lean_dec(v_fst_1831_);
                                    crate::leanh::lean_del_object(v___x_1829_);
                                    crate::leanh::lean_dec(v_fst_1827_);
                                    crate::leanh::lean_del_object(v___x_1820_);
                                    crate::leanh::lean_dec_ref(v_config_1779_);
                                    crate::leanh::lean_dec_ref(v_e_1778_);
                                    crate::leanh::lean_dec_ref(v_heq_1777_);
                                    crate::leanh::lean_dec(v___x_1776_);
                                    crate::leanh::lean_dec(v_mvarId_1775_);
                                    v_a_2297_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                                    v_isSharedCheck_2304_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2295_)) as u8;
                                    if v_isSharedCheck_2304_ == 0 {
                                        v___x_2299_ = v___x_2295_;
                                        v_isShared_2300_ = v_isSharedCheck_2304_;
                                        state = 58;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2297_);
                                        crate::leanh::lean_dec(v___x_2295_);
                                        v___x_2299_ = crate::leanh::lean_box(0);
                                        v_isShared_2300_ = v_isSharedCheck_2304_;
                                        state = 58;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_2292_);
                                crate::leanh::lean_dec(v_fst_2291_);
                                crate::leanh::lean_dec(v_fst_2290_);
                                crate::leanh::lean_dec(v___y_2269_);
                                crate::leanh::lean_dec_ref(v___y_2268_);
                                crate::leanh::lean_dec(v___y_2267_);
                                crate::leanh::lean_dec_ref(v___y_2266_);
                                crate::leanh::lean_del_object(v___x_1834_);
                                crate::leanh::lean_dec(v_fst_1831_);
                                crate::leanh::lean_del_object(v___x_1829_);
                                crate::leanh::lean_dec(v_fst_1827_);
                                crate::leanh::lean_del_object(v___x_1820_);
                                crate::leanh::lean_dec_ref(v_config_1779_);
                                crate::leanh::lean_dec_ref(v_e_1778_);
                                crate::leanh::lean_dec_ref(v_heq_1777_);
                                crate::leanh::lean_dec(v___x_1776_);
                                crate::leanh::lean_dec(v_mvarId_1775_);
                                v_a_2305_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
                                v_isSharedCheck_2312_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2293_)) as u8;
                                if v_isSharedCheck_2312_ == 0 {
                                    v___x_2307_ = v___x_2293_;
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 60;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2305_);
                                    crate::leanh::lean_dec(v___x_2293_);
                                    v___x_2307_ = crate::leanh::lean_box(0);
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 60;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2269_);
                    crate::leanh::lean_dec_ref(v___y_2268_);
                    crate::leanh::lean_dec(v___y_2267_);
                    crate::leanh::lean_dec_ref(v___y_2266_);
                    crate::leanh::lean_dec_ref(v_heqType_2265_);
                    crate::leanh::lean_dec_ref(v_heq_2264_);
                    crate::leanh::lean_del_object(v___x_1834_);
                    crate::leanh::lean_dec(v_fst_1831_);
                    crate::leanh::lean_del_object(v___x_1829_);
                    crate::leanh::lean_dec(v_fst_1827_);
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec_ref(v_config_1779_);
                    crate::leanh::lean_dec_ref(v_e_1778_);
                    crate::leanh::lean_dec_ref(v_heq_1777_);
                    crate::leanh::lean_dec(v___x_1776_);
                    crate::leanh::lean_dec(v_mvarId_1775_);
                    v_a_2313_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                    v_isSharedCheck_2320_ = (!crate::leanh::lean_is_exclusive(v___x_2270_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2315_ = v___x_2270_;
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 62;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2313_);
                        crate::leanh::lean_dec(v___x_2270_);
                        v___x_2315_ = crate::leanh::lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 62;
                        continue;
                    }
                }
            }
            56 => {
                if v_isShared_2280_ == 0 {
                    v___x_2282_ = v___x_2279_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
                    v___x_2282_ = v_reuseFailAlloc_2283_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_2282_;
            }
            58 => {
                if v_isShared_2300_ == 0 {
                    v___x_2302_ = v___x_2299_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_2303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
                    v___x_2302_ = v_reuseFailAlloc_2303_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_2302_;
            }
            60 => {
                if v_isShared_2308_ == 0 {
                    v___x_2310_ = v___x_2307_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
                    v___x_2310_ = v_reuseFailAlloc_2311_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_2310_;
            }
            62 => {
                if v_isShared_2316_ == 0 {
                    v___x_2318_ = v___x_2315_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_2318_;
            }
            64 => {
                if v_isShared_2335_ == 0 {
                    v___x_2337_ = v___x_2334_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
                    v___x_2337_ = v_reuseFailAlloc_2338_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2337_;
            }
            66 => {
                if v_isShared_2345_ == 0 {
                    v___x_2347_ = v___x_2344_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
                    v___x_2347_ = v_reuseFailAlloc_2348_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2347_;
            }
            68 => {
                if v_isShared_2354_ == 0 {
                    v___x_2356_ = v___x_2353_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_2356_;
            }
            70 => {
                if v_isShared_2362_ == 0 {
                    v___x_2364_ = v___x_2361_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
                    v___x_2364_ = v_reuseFailAlloc_2365_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_2364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_rewrite___lam__1___boxed(
    mut v_mvarId_2367_: *mut crate::leanh::LeanObject,
    mut v___x_2368_: *mut crate::leanh::LeanObject,
    mut v_heq_2369_: *mut crate::leanh::LeanObject,
    mut v_e_2370_: *mut crate::leanh::LeanObject,
    mut v_config_2371_: *mut crate::leanh::LeanObject,
    mut v_symm_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_symm_boxed_2378_: u8 = 0;
    let mut v_res_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_2378_ = (crate::leanh::lean_unbox(v_symm_2372_) as u8);
    v_res_2379_ = l_Lean_MVarId_rewrite___lam__1(
        v_mvarId_2367_,
        v___x_2368_,
        v_heq_2369_,
        v_e_2370_,
        v_config_2371_,
        v_symm_boxed_2378_,
        v___y_2373_,
        v___y_2374_,
        v___y_2375_,
        v___y_2376_,
    );
    return v_res_2379_;
}
pub unsafe fn l_Lean_MVarId_rewrite(
    mut v_mvarId_2383_: *mut crate::leanh::LeanObject,
    mut v_e_2384_: *mut crate::leanh::LeanObject,
    mut v_heq_2385_: *mut crate::leanh::LeanObject,
    mut v_symm_2386_: u8,
    mut v_config_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
    mut v_a_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_MVarId_rewrite___closed__1;
    v___x_2394_ = crate::leanh::lean_box((v_symm_2386_) as usize);
    crate::leanh::lean_inc(v_mvarId_2383_);
    v___f_2395_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_rewrite___lam__1___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2395_, 0, v_mvarId_2383_);
    crate::leanh::lean_closure_set(v___f_2395_, 1, v___x_2393_);
    crate::leanh::lean_closure_set(v___f_2395_, 2, v_heq_2385_);
    crate::leanh::lean_closure_set(v___f_2395_, 3, v_e_2384_);
    crate::leanh::lean_closure_set(v___f_2395_, 4, v_config_2387_);
    crate::leanh::lean_closure_set(v___f_2395_, 5, v___x_2394_);
    v___x_2396_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_rewrite_spec__9___redArg(
        v_mvarId_2383_,
        v___f_2395_,
        v_a_2388_,
        v_a_2389_,
        v_a_2390_,
        v_a_2391_,
    );
    return v___x_2396_;
}
pub unsafe fn l_Lean_MVarId_rewrite___boxed(
    mut v_mvarId_2397_: *mut crate::leanh::LeanObject,
    mut v_e_2398_: *mut crate::leanh::LeanObject,
    mut v_heq_2399_: *mut crate::leanh::LeanObject,
    mut v_symm_2400_: *mut crate::leanh::LeanObject,
    mut v_config_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_symm_boxed_2407_: u8 = 0;
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_symm_boxed_2407_ = (crate::leanh::lean_unbox(v_symm_2400_) as u8);
    v_res_2408_ = l_Lean_MVarId_rewrite(
        v_mvarId_2397_,
        v_e_2398_,
        v_heq_2399_,
        v_symm_boxed_2407_,
        v_config_2401_,
        v_a_2402_,
        v_a_2403_,
        v_a_2404_,
        v_a_2405_,
    );
    crate::leanh::lean_dec(v_a_2405_);
    crate::leanh::lean_dec_ref(v_a_2404_);
    crate::leanh::lean_dec(v_a_2403_);
    crate::leanh::lean_dec_ref(v_a_2402_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(
    mut v_mvarId_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___redArg(
        v_mvarId_2409_,
        v___y_2411_,
    );
    return v___x_2415_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0___boxed(
    mut v_mvarId_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2422_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0(
        v_mvarId_2416_,
        v___y_2417_,
        v___y_2418_,
        v___y_2419_,
        v___y_2420_,
    );
    crate::leanh::lean_dec(v___y_2420_);
    crate::leanh::lean_dec_ref(v___y_2419_);
    crate::leanh::lean_dec(v___y_2418_);
    crate::leanh::lean_dec_ref(v___y_2417_);
    crate::leanh::lean_dec(v_mvarId_2416_);
    return v_res_2422_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(
    mut v_00_u03b1_2423_: *mut crate::leanh::LeanObject,
    mut v_msg_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___redArg(
        v_msg_2424_,
        v___y_2425_,
        v___y_2426_,
        v___y_2427_,
        v___y_2428_,
    );
    return v___x_2430_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2___boxed(
    mut v_00_u03b1_2431_: *mut crate::leanh::LeanObject,
    mut v_msg_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_throwError___at___00Lean_MVarId_rewrite_spec__2(
        v_00_u03b1_2431_,
        v_msg_2432_,
        v___y_2433_,
        v___y_2434_,
        v___y_2435_,
        v___y_2436_,
    );
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(
    mut v_00_u03b1_2439_: *mut crate::leanh::LeanObject,
    mut v_name_2440_: *mut crate::leanh::LeanObject,
    mut v_bi_2441_: u8,
    mut v_type_2442_: *mut crate::leanh::LeanObject,
    mut v_k_2443_: *mut crate::leanh::LeanObject,
    mut v_kind_2444_: u8,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___redArg(v_name_2440_, v_bi_2441_, v_type_2442_, v_k_2443_, v_kind_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
    return v___x_2450_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11___boxed(
    mut v_00_u03b1_2451_: *mut crate::leanh::LeanObject,
    mut v_name_2452_: *mut crate::leanh::LeanObject,
    mut v_bi_2453_: *mut crate::leanh::LeanObject,
    mut v_type_2454_: *mut crate::leanh::LeanObject,
    mut v_k_2455_: *mut crate::leanh::LeanObject,
    mut v_kind_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2462_: u8 = 0;
    let mut v_kind_boxed_2463_: u8 = 0;
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2462_ = (crate::leanh::lean_unbox(v_bi_2453_) as u8);
    v_kind_boxed_2463_ = (crate::leanh::lean_unbox(v_kind_2456_) as u8);
    v_res_2464_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8_spec__11(v_00_u03b1_2451_, v_name_2452_, v_bi_boxed_2462_, v_type_2454_, v_k_2455_, v_kind_boxed_2463_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2459_);
    crate::leanh::lean_dec(v___y_2458_);
    crate::leanh::lean_dec_ref(v___y_2457_);
    return v_res_2464_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(
    mut v_00_u03b1_2465_: *mut crate::leanh::LeanObject,
    mut v_name_2466_: *mut crate::leanh::LeanObject,
    mut v_type_2467_: *mut crate::leanh::LeanObject,
    mut v_k_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___redArg(
        v_name_2466_,
        v_type_2467_,
        v_k_2468_,
        v___y_2469_,
        v___y_2470_,
        v___y_2471_,
        v___y_2472_,
    );
    return v___x_2474_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8___boxed(
    mut v_00_u03b1_2475_: *mut crate::leanh::LeanObject,
    mut v_name_2476_: *mut crate::leanh::LeanObject,
    mut v_type_2477_: *mut crate::leanh::LeanObject,
    mut v_k_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Lean_Meta_withLocalDeclD___at___00Lean_MVarId_rewrite_spec__8(
        v_00_u03b1_2475_,
        v_name_2476_,
        v_type_2477_,
        v_k_2478_,
        v___y_2479_,
        v___y_2480_,
        v___y_2481_,
        v___y_2482_,
    );
    crate::leanh::lean_dec(v___y_2482_);
    crate::leanh::lean_dec_ref(v___y_2481_);
    crate::leanh::lean_dec(v___y_2480_);
    crate::leanh::lean_dec_ref(v___y_2479_);
    return v_res_2484_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(
    mut v_00_u03b2_2485_: *mut crate::leanh::LeanObject,
    mut v_x_2486_: *mut crate::leanh::LeanObject,
    mut v_x_2487_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2488_: u8 = 0;
    v___x_2488_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___redArg(v_x_2486_, v_x_2487_);
    return v___x_2488_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0___boxed(
    mut v_00_u03b2_2489_: *mut crate::leanh::LeanObject,
    mut v_x_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2492_: u8 = 0;
    let mut v_r_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2492_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0(v_00_u03b2_2489_, v_x_2490_, v_x_2491_);
    crate::leanh::lean_dec(v_x_2491_);
    crate::leanh::lean_dec_ref(v_x_2490_);
    v_r_2493_ = crate::leanh::lean_box((v_res_2492_) as usize);
    return v_r_2493_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(
    mut v_00_u03b2_2494_: *mut crate::leanh::LeanObject,
    mut v_x_2495_: *mut crate::leanh::LeanObject,
    mut v_x_2496_: usize,
    mut v_x_2497_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2498_: u8 = 0;
    v___x_2498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___redArg(v_x_2495_, v_x_2496_, v_x_2497_);
    return v___x_2498_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b2_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
    mut v_x_2501_: *mut crate::leanh::LeanObject,
    mut v_x_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20113__boxed_2503_: usize = 0;
    let mut v_res_2504_: u8 = 0;
    let mut v_r_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20113__boxed_2503_ = crate::leanh::lean_unbox_usize(v_x_2501_);
    crate::leanh::lean_dec(v_x_2501_);
    v_res_2504_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4(v_00_u03b2_2499_, v_x_2500_, v_x_20113__boxed_2503_, v_x_2502_);
    crate::leanh::lean_dec(v_x_2502_);
    crate::leanh::lean_dec_ref(v_x_2500_);
    v_r_2505_ = crate::leanh::lean_box((v_res_2504_) as usize);
    return v_r_2505_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(
    mut v_00_u03b2_2506_: *mut crate::leanh::LeanObject,
    mut v_keys_2507_: *mut crate::leanh::LeanObject,
    mut v_vals_2508_: *mut crate::leanh::LeanObject,
    mut v_heq_2509_: *mut crate::leanh::LeanObject,
    mut v_i_2510_: *mut crate::leanh::LeanObject,
    mut v_k_2511_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2512_: u8 = 0;
    v___x_2512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___redArg(v_keys_2507_, v_i_2510_, v_k_2511_);
    return v___x_2512_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13___boxed(
    mut v_00_u03b2_2513_: *mut crate::leanh::LeanObject,
    mut v_keys_2514_: *mut crate::leanh::LeanObject,
    mut v_vals_2515_: *mut crate::leanh::LeanObject,
    mut v_heq_2516_: *mut crate::leanh::LeanObject,
    mut v_i_2517_: *mut crate::leanh::LeanObject,
    mut v_k_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2519_: u8 = 0;
    let mut v_r_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2519_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_rewrite_spec__0_spec__0_spec__4_spec__13(v_00_u03b2_2513_, v_keys_2514_, v_vals_2515_, v_heq_2516_, v_i_2517_, v_k_2518_);
    crate::leanh::lean_dec(v_k_2518_);
    crate::leanh::lean_dec_ref(v_vals_2515_);
    crate::leanh::lean_dec_ref(v_keys_2514_);
    v_r_2520_ = crate::leanh::lean_box((v_res_2519_) as usize);
    return v_r_2520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Rewrite(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
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
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Rewrite(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Rewrite(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
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
    res = initialize_Lean_Meta_KAbstract(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_BinderNameHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Rewrite(builtin);
}
