// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Lean.Meta.Tactic.Subst
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_headBeta, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isRawNatLit,
    l_Lean_Expr_mvarId_x21, l_Lean_FVarIdSet_insert, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalContext_getFVarIds, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqOfHEq, l_Lean_Meta_mkNoConfusion,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg, l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_saveState___redArg, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x27_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::MatchUtil::l_Lean_Meta_matchEqHEq_x3f;
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_MVarId_intro, l_Lean_Meta_intro1Core};
use crate::r#gen::Lean::Meta::Tactic::Subst::{
    initialize_Lean_Meta_Tactic_Subst, l_Lean_Meta_heqToEq,
    runtime_initialize_Lean_Meta_Tactic_Subst,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
pub static l_Lean_Meta_injectionCore___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_injectionCore___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__0_value: crate::leanh::LeanStringObject<
    46,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 110, 111, 67, 111, 110, 102, 117, 115,
        105, 111, 110, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 99, 111, 110, 115, 116,
        114, 117, 99, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__4_value: crate::leanh::LeanStringObject<
    46,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        101, 113, 117, 97, 108, 105, 116, 121, 32, 111, 102, 32, 99, 111, 110, 115, 116, 114, 117,
        99, 116, 111, 114, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 115, 32, 101,
        120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__8_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        115, 117, 98, 103, 111, 97, 108, 32, 119, 105, 116, 104, 32, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__10_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [32, 102, 105, 101, 108, 100, 115, 58, 10, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__12_value: crate::leanh::LeanStringObject<
    57,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 110, 111, 67, 111, 110, 102, 117, 115,
        105, 111, 110, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 99, 111, 110, 115, 116,
        114, 117, 99, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 116, 121, 112, 101, 58, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__14: u64 = 0;
pub static l_Lean_Meta_injectionCore___lam__1___closed__15_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        103, 111, 116, 32, 110, 111, 45, 99, 111, 110, 102, 117, 115, 105, 111, 110, 32, 112, 114,
        105, 110, 99, 105, 112, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__17_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [10, 111, 102, 32, 116, 121, 112, 101, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__19_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__19_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__21_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__22_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__21_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__25_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__26_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__27_value: crate::leanh::LeanStringObject<
    25,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        97, 112, 112, 108, 121, 105, 110, 103, 32, 110, 111, 67, 111, 110, 102, 117, 115, 105, 111,
        110, 32, 116, 111, 32, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__27_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__29_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 97, 116, 10, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__29_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__31_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [72, 69, 113, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__32_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__31_value)
                as *mut crate::leanh::LeanObject,
            13589827700912665667 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Meta_injectionCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12874249535713742015 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_injectionIntro___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_injectionIntro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_injectionIntro___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value)
                as *mut crate::leanh::LeanObject,
            142734480563613395 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_injectionIntro___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value)
                as *mut crate::leanh::LeanObject,
            15847151208953044930 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_injectionIntro___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12445953579901931010 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionIntro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionIntro___closed__3_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [105, 110, 116, 114, 111, 100, 117, 99, 105, 110, 103, 32, 0],
    };
static mut l_Lean_Meta_injectionIntro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionIntro___closed__5_value: crate::leanh::LeanStringObject<20> =
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
            32, 110, 101, 119, 32, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 32, 97, 116,
            10, 0,
        ],
    };
static mut l_Lean_Meta_injectionIntro___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value:
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
    m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        5163565424560827901 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 101, 120, 99,
        101, 101, 100, 101, 100, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2197290662802231936 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,223750332802285625 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16461794931444949472 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13255495822366105665 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,244446394462504164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value) as *mut crate::leanh::LeanObject,4458521110757701240 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value) as *mut crate::leanh::LeanObject,4208024077724612965 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17090328229070726430 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1583609249 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,4074967462205855788 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16020934614818583779 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6029258889307722371 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6712643992094006598 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(
    mut v_k_1801_: *mut crate::leanh::LeanObject,
    mut v_b_1802_: *mut crate::leanh::LeanObject,
    mut v_c_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1807_);
    crate::leanh::lean_inc_ref(v___y_1806_);
    crate::leanh::lean_inc(v___y_1805_);
    crate::leanh::lean_inc_ref(v___y_1804_);
    v___x_1809_ = crate::leanh::lean_apply_7(
        v_k_1801_,
        v_b_1802_,
        v_c_1803_,
        v___y_1804_,
        v___y_1805_,
        v___y_1806_,
        v___y_1807_,
        crate::leanh::lean_box(0),
    );
    return v___x_1809_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed(
    mut v_k_1810_: *mut crate::leanh::LeanObject,
    mut v_b_1811_: *mut crate::leanh::LeanObject,
    mut v_c_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(v_k_1810_, v_b_1811_, v_c_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    crate::leanh::lean_dec(v___y_1814_);
    crate::leanh::lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(
    mut v_type_1819_: *mut crate::leanh::LeanObject,
    mut v_k_1820_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1821_: u8,
    mut v_whnfType_1822_: u8,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_a_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1828_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1828_, 0, v_k_1820_);
                v___x_1829_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1819_,
                    v___f_1828_,
                    v_cleanupAnnotations_1821_,
                    v_whnfType_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                    v___y_1826_,
                );
                if crate::leanh::lean_obj_tag(v___x_1829_) == 0 {
                    v_a_1830_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1837_ = (!crate::leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1837_ == 0 {
                        v___x_1832_ = v___x_1829_;
                        v_isShared_1833_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1830_);
                        crate::leanh::lean_dec(v___x_1829_);
                        v___x_1832_ = crate::leanh::lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1838_ = crate::leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1845_ = (!crate::leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1845_ == 0 {
                        v___x_1840_ = v___x_1829_;
                        v_isShared_1841_ = v_isSharedCheck_1845_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1838_);
                        crate::leanh::lean_dec(v___x_1829_);
                        v___x_1840_ = crate::leanh::lean_box(0);
                        v_isShared_1841_ = v_isSharedCheck_1845_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1833_ == 0 {
                    v___x_1835_ = v___x_1832_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
                    v___x_1835_ = v_reuseFailAlloc_1836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1835_;
            }
            3 => {
                if v_isShared_1841_ == 0 {
                    v___x_1843_ = v___x_1840_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
                    v___x_1843_ = v_reuseFailAlloc_1844_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___boxed(
    mut v_type_1846_: *mut crate::leanh::LeanObject,
    mut v_k_1847_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1848_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1855_: u8 = 0;
    let mut v_whnfType_boxed_1856_: u8 = 0;
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1855_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1848_) as u8);
    v_whnfType_boxed_1856_ = (crate::leanh::lean_unbox(v_whnfType_1849_) as u8);
    v_res_1857_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1846_, v_k_1847_, v_cleanupAnnotations_boxed_1855_, v_whnfType_boxed_1856_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    crate::leanh::lean_dec(v___y_1851_);
    crate::leanh::lean_dec_ref(v___y_1850_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(
    mut v_00_u03b1_1858_: *mut crate::leanh::LeanObject,
    mut v_type_1859_: *mut crate::leanh::LeanObject,
    mut v_k_1860_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1861_: u8,
    mut v_whnfType_1862_: u8,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1859_, v_k_1860_, v_cleanupAnnotations_1861_, v_whnfType_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___boxed(
    mut v_00_u03b1_1869_: *mut crate::leanh::LeanObject,
    mut v_type_1870_: *mut crate::leanh::LeanObject,
    mut v_k_1871_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1872_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1879_: u8 = 0;
    let mut v_whnfType_boxed_1880_: u8 = 0;
    let mut v_res_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1879_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1872_) as u8);
    v_whnfType_boxed_1880_ = (crate::leanh::lean_unbox(v_whnfType_1873_) as u8);
    v_res_1881_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(
            v_00_u03b1_1869_,
            v_type_1870_,
            v_k_1871_,
            v_cleanupAnnotations_boxed_1879_,
            v_whnfType_boxed_1880_,
            v___y_1874_,
            v___y_1875_,
            v___y_1876_,
            v___y_1877_,
        );
    crate::leanh::lean_dec(v___y_1877_);
    crate::leanh::lean_dec_ref(v___y_1876_);
    crate::leanh::lean_dec(v___y_1875_);
    crate::leanh::lean_dec_ref(v___y_1874_);
    return v_res_1881_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(
    mut v_upperBound_1882_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1883_: *mut crate::leanh::LeanObject,
    mut v_xs_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_b_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1921_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1892_ = lean_nat_dec_lt(v_a_1885_, v_upperBound_1882_);
                if v___x_1892_ == 0 {
                    crate::leanh::lean_dec(v_a_1885_);
                    v___x_1893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1893_, 0, v_b_1886_);
                    return v___x_1893_;
                } else {
                    v_numParams_1894_ = crate::leanh::lean_ctor_get(v_ctorInfo_1883_, 3);
                    v___x_1895_ = l_Lean_instInhabitedExpr;
                    v___x_1896_ = lean_nat_add(v_numParams_1894_, v_a_1885_);
                    v___x_1897_ = lean_array_get_borrowed(v___x_1895_, v_xs_1884_, v___x_1896_);
                    crate::leanh::lean_dec(v___x_1896_);
                    crate::leanh::lean_inc(v___y_1890_);
                    crate::leanh::lean_inc_ref(v___y_1889_);
                    crate::leanh::lean_inc(v___y_1888_);
                    crate::leanh::lean_inc_ref(v___y_1887_);
                    crate::leanh::lean_inc(v___x_1897_);
                    v___x_1898_ = lean_infer_type(
                        v___x_1897_,
                        v___y_1887_,
                        v___y_1888_,
                        v___y_1889_,
                        v___y_1890_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1898_) == 0 {
                        v_a_1899_ = crate::leanh::lean_ctor_get(v___x_1898_, 0);
                        crate::leanh::lean_inc(v_a_1899_);
                        crate::leanh::lean_dec_ref_known(v___x_1898_, 1);
                        v___x_1900_ = l_Lean_Meta_isProp(
                            v_a_1899_,
                            v___y_1887_,
                            v___y_1888_,
                            v___y_1889_,
                            v___y_1890_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1900_) == 0 {
                            v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                            crate::leanh::lean_inc(v_a_1901_);
                            crate::leanh::lean_dec_ref_known(v___x_1900_, 1);
                            v___x_1907_ = (crate::leanh::lean_unbox(v_a_1901_) as u8);
                            crate::leanh::lean_dec(v_a_1901_);
                            if v___x_1907_ == 0 {
                                v_a_1903_ = v_b_1886_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1908_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1909_ = lean_nat_add(v_b_1886_, v___x_1908_);
                                crate::leanh::lean_dec(v_b_1886_);
                                v_a_1903_ = v___x_1909_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_b_1886_);
                            crate::leanh::lean_dec(v_a_1885_);
                            v_a_1910_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                            v_isSharedCheck_1917_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1900_)) as u8;
                            if v_isSharedCheck_1917_ == 0 {
                                v___x_1912_ = v___x_1900_;
                                v_isShared_1913_ = v_isSharedCheck_1917_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1910_);
                                crate::leanh::lean_dec(v___x_1900_);
                                v___x_1912_ = crate::leanh::lean_box(0);
                                v_isShared_1913_ = v_isSharedCheck_1917_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_1886_);
                        crate::leanh::lean_dec(v_a_1885_);
                        v_a_1918_ = crate::leanh::lean_ctor_get(v___x_1898_, 0);
                        v_isSharedCheck_1925_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1898_)) as u8;
                        if v_isSharedCheck_1925_ == 0 {
                            v___x_1920_ = v___x_1898_;
                            v_isShared_1921_ = v_isSharedCheck_1925_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1918_);
                            crate::leanh::lean_dec(v___x_1898_);
                            v___x_1920_ = crate::leanh::lean_box(0);
                            v_isShared_1921_ = v_isSharedCheck_1925_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1904_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1905_ = lean_nat_add(v_a_1885_, v___x_1904_);
                crate::leanh::lean_dec(v_a_1885_);
                v_a_1885_ = v___x_1905_;
                v_b_1886_ = v_a_1903_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1913_ == 0 {
                    v___x_1915_ = v___x_1912_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1915_;
            }
            4 => {
                if v_isShared_1921_ == 0 {
                    v___x_1923_ = v___x_1920_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
                    v___x_1923_ = v_reuseFailAlloc_1924_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(
    mut v_upperBound_1926_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1927_: *mut crate::leanh::LeanObject,
    mut v_xs_1928_: *mut crate::leanh::LeanObject,
    mut v_a_1929_: *mut crate::leanh::LeanObject,
    mut v_b_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1936_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(
            v_upperBound_1926_,
            v_ctorInfo_1927_,
            v_xs_1928_,
            v_a_1929_,
            v_b_1930_,
            v___y_1931_,
            v___y_1932_,
            v___y_1933_,
            v___y_1934_,
        );
    crate::leanh::lean_dec(v___y_1934_);
    crate::leanh::lean_dec_ref(v___y_1933_);
    crate::leanh::lean_dec(v___y_1932_);
    crate::leanh::lean_dec_ref(v___y_1931_);
    crate::leanh::lean_dec_ref(v_xs_1928_);
    crate::leanh::lean_dec_ref(v_ctorInfo_1927_);
    crate::leanh::lean_dec(v_upperBound_1926_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields___lam__0(
    mut v_numFields_1937_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1938_: *mut crate::leanh::LeanObject,
    mut v_xs_1939_: *mut crate::leanh::LeanObject,
    mut v_x_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
    mut v___y_1943_: *mut crate::leanh::LeanObject,
    mut v___y_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1947_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(
            v_numFields_1937_,
            v_ctorInfo_1938_,
            v_xs_1939_,
            v___x_1946_,
            v___x_1946_,
            v___y_1941_,
            v___y_1942_,
            v___y_1943_,
            v___y_1944_,
        );
    return v___x_1947_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(
    mut v_numFields_1948_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1949_: *mut crate::leanh::LeanObject,
    mut v_xs_1950_: *mut crate::leanh::LeanObject,
    mut v_x_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Lean_Meta_getCtorNumPropFields___lam__0(
        v_numFields_1948_,
        v_ctorInfo_1949_,
        v_xs_1950_,
        v_x_1951_,
        v___y_1952_,
        v___y_1953_,
        v___y_1954_,
        v___y_1955_,
    );
    crate::leanh::lean_dec(v___y_1955_);
    crate::leanh::lean_dec_ref(v___y_1954_);
    crate::leanh::lean_dec(v___y_1953_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    crate::leanh::lean_dec_ref(v_x_1951_);
    crate::leanh::lean_dec_ref(v_xs_1950_);
    crate::leanh::lean_dec_ref(v_ctorInfo_1949_);
    crate::leanh::lean_dec(v_numFields_1948_);
    return v_res_1957_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields(
    mut v_ctorInfo_1958_: *mut crate::leanh::LeanObject,
    mut v_a_1959_: *mut crate::leanh::LeanObject,
    mut v_a_1960_: *mut crate::leanh::LeanObject,
    mut v_a_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_1964_ = crate::leanh::lean_ctor_get(v_ctorInfo_1958_, 0);
    v_numFields_1965_ = crate::leanh::lean_ctor_get(v_ctorInfo_1958_, 4);
    crate::leanh::lean_inc(v_numFields_1965_);
    v_type_1966_ = crate::leanh::lean_ctor_get(v_toConstantVal_1964_, 2);
    crate::leanh::lean_inc_ref(v_type_1966_);
    v___f_1967_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_getCtorNumPropFields___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1967_, 0, v_numFields_1965_);
    crate::leanh::lean_closure_set(v___f_1967_, 1, v_ctorInfo_1958_);
    v___x_1968_ = 0;
    v___x_1969_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1966_, v___f_1967_, v___x_1968_, v___x_1968_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
    return v___x_1969_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields___boxed(
    mut v_ctorInfo_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_Meta_getCtorNumPropFields(
        v_ctorInfo_1970_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
    );
    crate::leanh::lean_dec(v_a_1974_);
    crate::leanh::lean_dec_ref(v_a_1973_);
    crate::leanh::lean_dec(v_a_1972_);
    crate::leanh::lean_dec_ref(v_a_1971_);
    return v_res_1976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(
    mut v_upperBound_1977_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1978_: *mut crate::leanh::LeanObject,
    mut v_xs_1979_: *mut crate::leanh::LeanObject,
    mut v_inst_1980_: *mut crate::leanh::LeanObject,
    mut v_R_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_b_1983_: *mut crate::leanh::LeanObject,
    mut v_c_1984_: *mut crate::leanh::LeanObject,
    mut v___y_1985_: *mut crate::leanh::LeanObject,
    mut v___y_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1990_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(
            v_upperBound_1977_,
            v_ctorInfo_1978_,
            v_xs_1979_,
            v_a_1982_,
            v_b_1983_,
            v___y_1985_,
            v___y_1986_,
            v___y_1987_,
            v___y_1988_,
        );
    return v___x_1990_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___boxed(
    mut v_upperBound_1991_: *mut crate::leanh::LeanObject,
    mut v_ctorInfo_1992_: *mut crate::leanh::LeanObject,
    mut v_xs_1993_: *mut crate::leanh::LeanObject,
    mut v_inst_1994_: *mut crate::leanh::LeanObject,
    mut v_R_1995_: *mut crate::leanh::LeanObject,
    mut v_a_1996_: *mut crate::leanh::LeanObject,
    mut v_b_1997_: *mut crate::leanh::LeanObject,
    mut v_c_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(
        v_upperBound_1991_,
        v_ctorInfo_1992_,
        v_xs_1993_,
        v_inst_1994_,
        v_R_1995_,
        v_a_1996_,
        v_b_1997_,
        v_c_1998_,
        v___y_1999_,
        v___y_2000_,
        v___y_2001_,
        v___y_2002_,
    );
    crate::leanh::lean_dec(v___y_2002_);
    crate::leanh::lean_dec_ref(v___y_2001_);
    crate::leanh::lean_dec(v___y_2000_);
    crate::leanh::lean_dec_ref(v___y_1999_);
    crate::leanh::lean_dec_ref(v_xs_1993_);
    crate::leanh::lean_dec_ref(v_ctorInfo_1992_);
    crate::leanh::lean_dec(v_upperBound_1991_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorIdx(
    mut v_x_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2005_) == 0 {
        let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2006_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2006_;
    } else {
        let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2007_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2007_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorIdx___boxed(
    mut v_x_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_Meta_InjectionResultCore_ctorIdx(v_x_2008_);
    crate::leanh::lean_dec(v_x_2008_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim___redArg(
    mut v_t_2010_: *mut crate::leanh::LeanObject,
    mut v_k_2011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2010_) == 0 {
        return v_k_2011_;
    } else {
        let mut v_mvarId_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_numNewEqs_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_2012_ = crate::leanh::lean_ctor_get(v_t_2010_, 0);
        crate::leanh::lean_inc(v_mvarId_2012_);
        v_numNewEqs_2013_ = crate::leanh::lean_ctor_get(v_t_2010_, 1);
        crate::leanh::lean_inc(v_numNewEqs_2013_);
        crate::leanh::lean_dec_ref_known(v_t_2010_, 2);
        v___x_2014_ = crate::leanh::lean_apply_2(v_k_2011_, v_mvarId_2012_, v_numNewEqs_2013_);
        return v___x_2014_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim(
    mut v_motive_2015_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2016_: *mut crate::leanh::LeanObject,
    mut v_t_2017_: *mut crate::leanh::LeanObject,
    mut v_h_2018_: *mut crate::leanh::LeanObject,
    mut v_k_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2017_, v_k_2019_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim___boxed(
    mut v_motive_2021_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2022_: *mut crate::leanh::LeanObject,
    mut v_t_2023_: *mut crate::leanh::LeanObject,
    mut v_h_2024_: *mut crate::leanh::LeanObject,
    mut v_k_2025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Lean_Meta_InjectionResultCore_ctorElim(
        v_motive_2021_,
        v_ctorIdx_2022_,
        v_t_2023_,
        v_h_2024_,
        v_k_2025_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2022_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_solved_elim___redArg(
    mut v_t_2027_: *mut crate::leanh::LeanObject,
    mut v_solved_2028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2027_, v_solved_2028_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_solved_elim(
    mut v_motive_2030_: *mut crate::leanh::LeanObject,
    mut v_t_2031_: *mut crate::leanh::LeanObject,
    mut v_h_2032_: *mut crate::leanh::LeanObject,
    mut v_solved_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2031_, v_solved_2033_);
    return v___x_2034_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(
    mut v_t_2035_: *mut crate::leanh::LeanObject,
    mut v_subgoal_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2037_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2035_, v_subgoal_2036_);
    return v___x_2037_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_subgoal_elim(
    mut v_motive_2038_: *mut crate::leanh::LeanObject,
    mut v_t_2039_: *mut crate::leanh::LeanObject,
    mut v_h_2040_: *mut crate::leanh::LeanObject,
    mut v_subgoal_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2039_, v_subgoal_2041_);
    return v___x_2042_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
    mut v_mvarId_2043_: *mut crate::leanh::LeanObject,
    mut v_x_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
    mut v___y_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2043_,
                    v_x_2044_,
                    v___y_2045_,
                    v___y_2046_,
                    v___y_2047_,
                    v___y_2048_,
                );
                if crate::leanh::lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2050_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2051_);
                        crate::leanh::lean_dec(v___x_2050_);
                        v___x_2053_ = crate::leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2059_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2066_ = (!crate::leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2061_ = v___x_2050_;
                        v_isShared_2062_ = v_isSharedCheck_2066_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2059_);
                        crate::leanh::lean_dec(v___x_2050_);
                        v___x_2061_ = crate::leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2066_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2056_;
            }
            3 => {
                if v_isShared_2062_ == 0 {
                    v___x_2064_ = v___x_2061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg___boxed(
    mut v_mvarId_2067_: *mut crate::leanh::LeanObject,
    mut v_x_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2074_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
        v_mvarId_2067_,
        v_x_2068_,
        v___y_2069_,
        v___y_2070_,
        v___y_2071_,
        v___y_2072_,
    );
    crate::leanh::lean_dec(v___y_2072_);
    crate::leanh::lean_dec_ref(v___y_2071_);
    crate::leanh::lean_dec(v___y_2070_);
    crate::leanh::lean_dec_ref(v___y_2069_);
    return v_res_2074_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(
    mut v_00_u03b1_2075_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2076_: *mut crate::leanh::LeanObject,
    mut v_x_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
        v_mvarId_2076_,
        v_x_2077_,
        v___y_2078_,
        v___y_2079_,
        v___y_2080_,
        v___y_2081_,
    );
    return v___x_2083_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___boxed(
    mut v_00_u03b1_2084_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2085_: *mut crate::leanh::LeanObject,
    mut v_x_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
    mut v___y_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
    mut v___y_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(
        v_00_u03b1_2084_,
        v_mvarId_2085_,
        v_x_2086_,
        v___y_2087_,
        v___y_2088_,
        v___y_2089_,
        v___y_2090_,
    );
    crate::leanh::lean_dec(v___y_2090_);
    crate::leanh::lean_dec_ref(v___y_2089_);
    crate::leanh::lean_dec(v___y_2088_);
    crate::leanh::lean_dec_ref(v___y_2087_);
    return v_res_2092_;
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__0(
    mut v___x_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2103_: u8 = 0;
    v_options_2102_ = crate::leanh::lean_ctor_get(v___y_2099_, 2);
    v_hasTrace_2103_ = crate::leanh::lean_ctor_get_uint8(
        v_options_2102_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_2103_ == 0 {
        let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2096_);
        v___x_2104_ = crate::leanh::lean_box((v_hasTrace_2103_) as usize);
        v___x_2105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2105_, 0, v___x_2104_);
        return v___x_2105_;
    } else {
        let mut v_inheritedTraceOptions_2106_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: u8 = 0;
        let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_2106_ = crate::leanh::lean_ctor_get(v___y_2099_, 13);
        v___x_2107_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
        v___x_2108_ = l_Lean_Name_append(v___x_2107_, v___x_2096_);
        v___x_2109_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_2106_,
            v_options_2102_,
            v___x_2108_,
        );
        crate::leanh::lean_dec(v___x_2108_);
        v___x_2110_ = crate::leanh::lean_box((v___x_2109_) as usize);
        v___x_2111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2111_, 0, v___x_2110_);
        return v___x_2111_;
    }
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__0___boxed(
    mut v___x_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2118_ = l_Lean_Meta_injectionCore___lam__0(
        v___x_2112_,
        v___y_2113_,
        v___y_2114_,
        v___y_2115_,
        v___y_2116_,
    );
    crate::leanh::lean_dec(v___y_2116_);
    crate::leanh::lean_dec_ref(v___y_2115_);
    crate::leanh::lean_dec(v___y_2114_);
    crate::leanh::lean_dec_ref(v___y_2113_);
    return v_res_2118_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(
    mut v_msgData_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v___y_2122_: *mut crate::leanh::LeanObject,
    mut v___y_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = lean_st_ref_get(v___y_2123_);
    v_env_2126_ = crate::leanh::lean_ctor_get(v___x_2125_, 0);
    crate::leanh::lean_inc_ref(v_env_2126_);
    crate::leanh::lean_dec(v___x_2125_);
    v___x_2127_ = lean_st_ref_get(v___y_2121_);
    v_mctx_2128_ = crate::leanh::lean_ctor_get(v___x_2127_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2128_);
    crate::leanh::lean_dec(v___x_2127_);
    v_lctx_2129_ = crate::leanh::lean_ctor_get(v___y_2120_, 2);
    v_options_2130_ = crate::leanh::lean_ctor_get(v___y_2122_, 2);
    crate::leanh::lean_inc_ref(v_options_2130_);
    crate::leanh::lean_inc_ref(v_lctx_2129_);
    v___x_2131_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2131_, 0, v_env_2126_);
    crate::leanh::lean_ctor_set(v___x_2131_, 1, v_mctx_2128_);
    crate::leanh::lean_ctor_set(v___x_2131_, 2, v_lctx_2129_);
    crate::leanh::lean_ctor_set(v___x_2131_, 3, v_options_2130_);
    v___x_2132_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
    crate::leanh::lean_ctor_set(v___x_2132_, 1, v_msgData_2119_);
    v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    return v___x_2133_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(
    mut v_msgData_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    crate::leanh::lean_dec(v___y_2138_);
    crate::leanh::lean_dec_ref(v___y_2137_);
    crate::leanh::lean_dec(v___y_2136_);
    crate::leanh::lean_dec_ref(v___y_2135_);
    return v_res_2140_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0() -> f64 {
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: f64 = 0.0;
    v___x_2141_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2142_ = lean_float_of_nat(v___x_2141_);
    return v___x_2142_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
    mut v_cls_2146_: *mut crate::leanh::LeanObject,
    mut v_msg_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v_tid_2172_: u64 = 0;
    let mut v_traces_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: f64 = 0.0;
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2153_ = crate::leanh::lean_ctor_get(v___y_2150_, 5);
                v___x_2154_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
                v_a_2155_ = crate::leanh::lean_ctor_get(v___x_2154_, 0);
                v_isSharedCheck_2199_ = (!crate::leanh::lean_is_exclusive(v___x_2154_)) as u8;
                if v_isSharedCheck_2199_ == 0 {
                    v___x_2157_ = v___x_2154_;
                    v_isShared_2158_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2155_);
                    crate::leanh::lean_dec(v___x_2154_);
                    v___x_2157_ = crate::leanh::lean_box(0);
                    v_isShared_2158_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2159_ = lean_st_ref_take(v___y_2151_);
                v_traceState_2160_ = crate::leanh::lean_ctor_get(v___x_2159_, 4);
                v_env_2161_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                v_nextMacroScope_2162_ = crate::leanh::lean_ctor_get(v___x_2159_, 1);
                v_ngen_2163_ = crate::leanh::lean_ctor_get(v___x_2159_, 2);
                v_auxDeclNGen_2164_ = crate::leanh::lean_ctor_get(v___x_2159_, 3);
                v_cache_2165_ = crate::leanh::lean_ctor_get(v___x_2159_, 5);
                v_messages_2166_ = crate::leanh::lean_ctor_get(v___x_2159_, 6);
                v_infoState_2167_ = crate::leanh::lean_ctor_get(v___x_2159_, 7);
                v_snapshotTasks_2168_ = crate::leanh::lean_ctor_get(v___x_2159_, 8);
                v_isSharedCheck_2198_ = (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2170_ = v___x_2159_;
                    v_isShared_2171_ = v_isSharedCheck_2198_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2168_);
                    crate::leanh::lean_inc(v_infoState_2167_);
                    crate::leanh::lean_inc(v_messages_2166_);
                    crate::leanh::lean_inc(v_cache_2165_);
                    crate::leanh::lean_inc(v_traceState_2160_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2164_);
                    crate::leanh::lean_inc(v_ngen_2163_);
                    crate::leanh::lean_inc(v_nextMacroScope_2162_);
                    crate::leanh::lean_inc(v_env_2161_);
                    crate::leanh::lean_dec(v___x_2159_);
                    v___x_2170_ = crate::leanh::lean_box(0);
                    v_isShared_2171_ = v_isSharedCheck_2198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2172_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2160_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2173_ = crate::leanh::lean_ctor_get(v_traceState_2160_, 0);
                v_isSharedCheck_2197_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2160_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2175_ = v_traceState_2160_;
                    v_isShared_2176_ = v_isSharedCheck_2197_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2173_);
                    crate::leanh::lean_dec(v_traceState_2160_);
                    v___x_2175_ = crate::leanh::lean_box(0);
                    v_isShared_2176_ = v_isSharedCheck_2197_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2177_ = crate::leanh::lean_box(0);
                v___x_2178_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0,
                );
                v___x_2179_ = 0;
                v___x_2180_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1;
                v___x_2181_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2181_, 0, v_cls_2146_);
                crate::leanh::lean_ctor_set(v___x_2181_, 1, v___x_2177_);
                crate::leanh::lean_ctor_set(v___x_2181_, 2, v___x_2180_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2181_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2178_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2181_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2178_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2181_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2179_,
                );
                v___x_2182_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2;
                v___x_2183_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2181_);
                crate::leanh::lean_ctor_set(v___x_2183_, 1, v_a_2155_);
                crate::leanh::lean_ctor_set(v___x_2183_, 2, v___x_2182_);
                crate::leanh::lean_inc(v_ref_2153_);
                v___x_2184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2184_, 0, v_ref_2153_);
                crate::leanh::lean_ctor_set(v___x_2184_, 1, v___x_2183_);
                v___x_2185_ = l_Lean_PersistentArray_push___redArg(v_traces_2173_, v___x_2184_);
                if v_isShared_2176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2175_, 0, v___x_2185_);
                    v___x_2187_ = v___x_2175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2185_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2196_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2172_,
                    );
                    v___x_2187_ = v_reuseFailAlloc_2196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2170_, 4, v___x_2187_);
                    v___x_2189_ = v___x_2170_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_env_2161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_nextMacroScope_2162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_ngen_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_auxDeclNGen_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 4, v___x_2187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 5, v_cache_2165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 6, v_messages_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 7, v_infoState_2167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 8, v_snapshotTasks_2168_);
                    v___x_2189_ = v_reuseFailAlloc_2195_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2190_ = lean_st_ref_set(v___y_2151_, v___x_2189_);
                v___x_2191_ = crate::leanh::lean_box(0);
                if v_isShared_2158_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2191_);
                    v___x_2193_ = v___x_2157_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
                    v___x_2193_ = v_reuseFailAlloc_2194_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___boxed(
    mut v_cls_2200_: *mut crate::leanh::LeanObject,
    mut v_msg_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2207_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
        v_cls_2200_,
        v_msg_2201_,
        v___y_2202_,
        v___y_2203_,
        v___y_2204_,
        v___y_2205_,
    );
    crate::leanh::lean_dec(v___y_2205_);
    crate::leanh::lean_dec_ref(v___y_2204_);
    crate::leanh::lean_dec(v___y_2203_);
    crate::leanh::lean_dec_ref(v___y_2202_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_x_2208_: *mut crate::leanh::LeanObject,
    mut v_x_2209_: *mut crate::leanh::LeanObject,
    mut v_x_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2212_ = crate::leanh::lean_ctor_get(v_x_2208_, 0);
                v_vs_2213_ = crate::leanh::lean_ctor_get(v_x_2208_, 1);
                v_isSharedCheck_2237_ = (!crate::leanh::lean_is_exclusive(v_x_2208_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v___x_2215_ = v_x_2208_;
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2213_);
                    crate::leanh::lean_inc(v_ks_2212_);
                    crate::leanh::lean_dec(v_x_2208_);
                    v___x_2215_ = crate::leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = lean_array_get_size(v_ks_2212_);
                v___x_2218_ = lean_nat_dec_lt(v_x_2209_, v___x_2217_);
                if v___x_2218_ == 0 {
                    crate::leanh::lean_dec(v_x_2209_);
                    v___x_2219_ = lean_array_push(v_ks_2212_, v_x_2210_);
                    v___x_2220_ = lean_array_push(v_vs_2213_, v_x_2211_);
                    if v_isShared_2216_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2220_);
                        crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2219_);
                        v___x_2222_ = v___x_2215_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2223_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2220_);
                        v___x_2222_ = v_reuseFailAlloc_2223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2224_ = lean_array_fget_borrowed(v_ks_2212_, v_x_2209_);
                    v___x_2225_ = l_Lean_instBEqMVarId_beq(v_x_2210_, v_k_x27_2224_);
                    if v___x_2225_ == 0 {
                        if v_isShared_2216_ == 0 {
                            v___x_2227_ = v___x_2215_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2231_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_ks_2212_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_vs_2213_);
                            v___x_2227_ = v_reuseFailAlloc_2231_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2232_ = lean_array_fset(v_ks_2212_, v_x_2209_, v_x_2210_);
                        v___x_2233_ = lean_array_fset(v_vs_2213_, v_x_2209_, v_x_2211_);
                        crate::leanh::lean_dec(v_x_2209_);
                        if v_isShared_2216_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2233_);
                            crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2232_);
                            v___x_2235_ = v___x_2215_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2236_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
                            v___x_2235_ = v_reuseFailAlloc_2236_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2222_;
            }
            3 => {
                v___x_2228_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2229_ = lean_nat_add(v_x_2209_, v___x_2228_);
                crate::leanh::lean_dec(v_x_2209_);
                v_x_2208_ = v___x_2227_;
                v_x_2209_ = v___x_2229_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_n_2238_: *mut crate::leanh::LeanObject,
    mut v_k_2239_: *mut crate::leanh::LeanObject,
    mut v_v_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_2238_, v___x_2241_, v_k_2239_, v_v_2240_);
    return v___x_2242_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: usize = 0;
    v___x_2243_ = 5usize;
    v___x_2244_ = 1usize;
    v___x_2245_ = lean_usize_shift_left(v___x_2244_, v___x_2243_);
    return v___x_2245_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2246_: usize = 0;
    let mut v___x_2247_: usize = 0;
    let mut v___x_2248_: usize = 0;
    v___x_2246_ = 1usize;
    v___x_2247_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_2248_ = lean_usize_sub(v___x_2247_, v___x_2246_);
    return v___x_2248_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: usize,
    mut v_x_2252_: usize,
    mut v_x_2253_: *mut crate::leanh::LeanObject,
    mut v_x_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: usize = 0;
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v_j_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_v_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_node_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: u8 = 0;
    let mut v_ks_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2250_) == 0 {
                    v_es_2255_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                    v___x_2256_ = 5usize;
                    v___x_2257_ = 1usize;
                    v___x_2258_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2259_ = lean_usize_land(v_x_2251_, v___x_2258_);
                    v_j_2260_ = lean_usize_to_nat(v___x_2259_);
                    v___x_2261_ = lean_array_get_size(v_es_2255_);
                    v___x_2262_ = lean_nat_dec_lt(v_j_2260_, v___x_2261_);
                    if v___x_2262_ == 0 {
                        crate::leanh::lean_dec(v_j_2260_);
                        crate::leanh::lean_dec(v_x_2254_);
                        crate::leanh::lean_dec(v_x_2253_);
                        return v_x_2250_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2255_);
                        v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v_x_2250_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                            crate::leanh::lean_dec(v_unused_2300_);
                            v___x_2264_ = v_x_2250_;
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2250_);
                            v___x_2264_ = crate::leanh::lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2301_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                    v_vs_2302_ = crate::leanh::lean_ctor_get(v_x_2250_, 1);
                    v_isSharedCheck_2322_ = (!crate::leanh::lean_is_exclusive(v_x_2250_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2304_ = v_x_2250_;
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2302_);
                        crate::leanh::lean_inc(v_ks_2301_);
                        crate::leanh::lean_dec(v_x_2250_);
                        v___x_2304_ = crate::leanh::lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2266_ = lean_array_fget(v_es_2255_, v_j_2260_);
                v___x_2267_ = crate::leanh::lean_box(0);
                v_xs_x27_2268_ = lean_array_fset(v_es_2255_, v_j_2260_, v___x_2267_);
                match crate::leanh::lean_obj_tag(v_v_2266_) {
                    0 => {
                        v_key_2275_ = crate::leanh::lean_ctor_get(v_v_2266_, 0);
                        v_val_2276_ = crate::leanh::lean_ctor_get(v_v_2266_, 1);
                        v_isSharedCheck_2286_ = (!crate::leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2286_ == 0 {
                            v___x_2278_ = v_v_2266_;
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2276_);
                            crate::leanh::lean_inc(v_key_2275_);
                            crate::leanh::lean_dec(v_v_2266_);
                            v___x_2278_ = crate::leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2287_ = crate::leanh::lean_ctor_get(v_v_2266_, 0);
                        v_isSharedCheck_2297_ = (!crate::leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2289_ = v_v_2266_;
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2287_);
                            crate::leanh::lean_dec(v_v_2266_);
                            v___x_2289_ = crate::leanh::lean_box(0);
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2298_, 0, v_x_2253_);
                        crate::leanh::lean_ctor_set(v___x_2298_, 1, v_x_2254_);
                        v___y_2270_ = v___x_2298_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2271_ = lean_array_fset(v_xs_x27_2268_, v_j_2260_, v___y_2270_);
                crate::leanh::lean_dec(v_j_2260_);
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2273_;
            }
            4 => {
                v___x_2280_ = l_Lean_instBEqMVarId_beq(v_x_2253_, v_key_2275_);
                if v___x_2280_ == 0 {
                    crate::leanh::lean_del_object(v___x_2278_);
                    v___x_2281_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2275_,
                        v_val_2276_,
                        v_x_2253_,
                        v_x_2254_,
                    );
                    v___x_2282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
                    v___y_2270_ = v___x_2282_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2276_);
                    crate::leanh::lean_dec(v_key_2275_);
                    if v_isShared_2279_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2278_, 1, v_x_2254_);
                        crate::leanh::lean_ctor_set(v___x_2278_, 0, v_x_2253_);
                        v___x_2284_ = v___x_2278_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_x_2253_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_x_2254_);
                        v___x_2284_ = v_reuseFailAlloc_2285_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2270_ = v___x_2284_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2291_ = lean_usize_shift_right(v_x_2251_, v___x_2256_);
                v___x_2292_ = lean_usize_add(v_x_2252_, v___x_2257_);
                v___x_2293_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_node_2287_, v___x_2291_, v___x_2292_, v_x_2253_, v_x_2254_);
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2293_);
                    v___x_2295_ = v___x_2289_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2270_ = v___x_2295_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2305_ == 0 {
                    v___x_2307_ = v___x_2304_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_ks_2301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_vs_2302_);
                    v___x_2307_ = v_reuseFailAlloc_2321_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2308_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v___x_2307_, v_x_2253_, v_x_2254_);
                v___x_2316_ = 7usize;
                v___x_2317_ = lean_usize_dec_le(v___x_2316_, v_x_2252_);
                if v___x_2317_ == 0 {
                    v___x_2318_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2308_);
                    v___x_2319_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
                    crate::leanh::lean_dec(v___x_2318_);
                    v___y_2310_ = v___x_2320_;
                    state = 10;
                    continue;
                } else {
                    v___y_2310_ = v___x_2317_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2310_ == 0 {
                    v_ks_2311_ = crate::leanh::lean_ctor_get(v_newNode_2308_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2311_);
                    v_vs_2312_ = crate::leanh::lean_ctor_get(v_newNode_2308_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2312_);
                    crate::leanh::lean_dec_ref(v_newNode_2308_);
                    v___x_2313_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2252_, v_ks_2311_, v_vs_2312_, v___x_2313_, v___x_2314_);
                    crate::leanh::lean_dec_ref(v_vs_2312_);
                    crate::leanh::lean_dec_ref(v_ks_2311_);
                    return v___x_2315_;
                } else {
                    return v_newNode_2308_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_depth_2323_: usize,
    mut v_keys_2324_: *mut crate::leanh::LeanObject,
    mut v_vals_2325_: *mut crate::leanh::LeanObject,
    mut v_i_2326_: *mut crate::leanh::LeanObject,
    mut v_entries_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v_k_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_h_2333_: usize = 0;
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v_h_2339_: usize = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2328_ = lean_array_get_size(v_keys_2324_);
                v___x_2329_ = lean_nat_dec_lt(v_i_2326_, v___x_2328_);
                if v___x_2329_ == 0 {
                    crate::leanh::lean_dec(v_i_2326_);
                    return v_entries_2327_;
                } else {
                    v_k_2330_ = lean_array_fget_borrowed(v_keys_2324_, v_i_2326_);
                    v_v_2331_ = lean_array_fget_borrowed(v_vals_2325_, v_i_2326_);
                    v___x_2332_ = l_Lean_instHashableMVarId_hash(v_k_2330_);
                    v_h_2333_ = lean_uint64_to_usize(v___x_2332_);
                    v___x_2334_ = 5usize;
                    v___x_2335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2336_ = 1usize;
                    v___x_2337_ = lean_usize_sub(v_depth_2323_, v___x_2336_);
                    v___x_2338_ = lean_usize_mul(v___x_2334_, v___x_2337_);
                    v_h_2339_ = lean_usize_shift_right(v_h_2333_, v___x_2338_);
                    v___x_2340_ = lean_nat_add(v_i_2326_, v___x_2335_);
                    crate::leanh::lean_dec(v_i_2326_);
                    crate::leanh::lean_inc(v_v_2331_);
                    crate::leanh::lean_inc(v_k_2330_);
                    v___x_2341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_entries_2327_, v_h_2339_, v_depth_2323_, v_k_2330_, v_v_2331_);
                    v_i_2326_ = v___x_2340_;
                    v_entries_2327_ = v___x_2341_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_depth_2343_: *mut crate::leanh::LeanObject,
    mut v_keys_2344_: *mut crate::leanh::LeanObject,
    mut v_vals_2345_: *mut crate::leanh::LeanObject,
    mut v_i_2346_: *mut crate::leanh::LeanObject,
    mut v_entries_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2348_: usize = 0;
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2348_ = crate::leanh::lean_unbox_usize(v_depth_2343_);
    crate::leanh::lean_dec(v_depth_2343_);
    v_res_2349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_2348_, v_keys_2344_, v_vals_2345_, v_i_2346_, v_entries_2347_);
    crate::leanh::lean_dec_ref(v_vals_2345_);
    crate::leanh::lean_dec_ref(v_keys_2344_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_x_2352_: *mut crate::leanh::LeanObject,
    mut v_x_2353_: *mut crate::leanh::LeanObject,
    mut v_x_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_16678__boxed_2355_: usize = 0;
    let mut v_x_16679__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_16678__boxed_2355_ = crate::leanh::lean_unbox_usize(v_x_2351_);
    crate::leanh::lean_dec(v_x_2351_);
    v_x_16679__boxed_2356_ = crate::leanh::lean_unbox_usize(v_x_2352_);
    crate::leanh::lean_dec(v_x_2352_);
    v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2350_, v_x_16678__boxed_2355_, v_x_16679__boxed_2356_, v_x_2353_, v_x_2354_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(
    mut v_x_2358_: *mut crate::leanh::LeanObject,
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_x_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2361_: u64 = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ = l_Lean_instHashableMVarId_hash(v_x_2359_);
    v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
    v___x_2363_ = 1usize;
    v___x_2364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2358_, v___x_2362_, v___x_2363_, v_x_2359_, v_x_2360_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
    mut v_mvarId_2365_: *mut crate::leanh::LeanObject,
    mut v_val_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v_depth_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2369_ = lean_st_ref_take(v___y_2367_);
                v_mctx_2370_ = crate::leanh::lean_ctor_get(v___x_2369_, 0);
                v_cache_2371_ = crate::leanh::lean_ctor_get(v___x_2369_, 1);
                v_zetaDeltaFVarIds_2372_ = crate::leanh::lean_ctor_get(v___x_2369_, 2);
                v_postponed_2373_ = crate::leanh::lean_ctor_get(v___x_2369_, 3);
                v_diag_2374_ = crate::leanh::lean_ctor_get(v___x_2369_, 4);
                v_isSharedCheck_2402_ = (!crate::leanh::lean_is_exclusive(v___x_2369_)) as u8;
                if v_isSharedCheck_2402_ == 0 {
                    v___x_2376_ = v___x_2369_;
                    v_isShared_2377_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2374_);
                    crate::leanh::lean_inc(v_postponed_2373_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2372_);
                    crate::leanh::lean_inc(v_cache_2371_);
                    crate::leanh::lean_inc(v_mctx_2370_);
                    crate::leanh::lean_dec(v___x_2369_);
                    v___x_2376_ = crate::leanh::lean_box(0);
                    v_isShared_2377_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2378_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 0);
                v_levelAssignDepth_2379_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 1);
                v_lmvarCounter_2380_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 2);
                v_mvarCounter_2381_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 3);
                v_lDecls_2382_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 4);
                v_decls_2383_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 5);
                v_userNames_2384_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 6);
                v_lAssignment_2385_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 7);
                v_eAssignment_2386_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 8);
                v_dAssignment_2387_ = crate::leanh::lean_ctor_get(v_mctx_2370_, 9);
                v_isSharedCheck_2401_ = (!crate::leanh::lean_is_exclusive(v_mctx_2370_)) as u8;
                if v_isSharedCheck_2401_ == 0 {
                    v___x_2389_ = v_mctx_2370_;
                    v_isShared_2390_ = v_isSharedCheck_2401_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2387_);
                    crate::leanh::lean_inc(v_eAssignment_2386_);
                    crate::leanh::lean_inc(v_lAssignment_2385_);
                    crate::leanh::lean_inc(v_userNames_2384_);
                    crate::leanh::lean_inc(v_decls_2383_);
                    crate::leanh::lean_inc(v_lDecls_2382_);
                    crate::leanh::lean_inc(v_mvarCounter_2381_);
                    crate::leanh::lean_inc(v_lmvarCounter_2380_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2379_);
                    crate::leanh::lean_inc(v_depth_2378_);
                    crate::leanh::lean_dec(v_mctx_2370_);
                    v___x_2389_ = crate::leanh::lean_box(0);
                    v_isShared_2390_ = v_isSharedCheck_2401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2391_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_2386_, v_mvarId_2365_, v_val_2366_);
                if v_isShared_2390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2389_, 8, v___x_2391_);
                    v___x_2393_ = v___x_2389_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_depth_2378_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2400_,
                        1,
                        v_levelAssignDepth_2379_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_lmvarCounter_2380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_mvarCounter_2381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_lDecls_2382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 5, v_decls_2383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_userNames_2384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_lAssignment_2385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 8, v___x_2391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 9, v_dAssignment_2387_);
                    v___x_2393_ = v_reuseFailAlloc_2400_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2376_, 0, v___x_2393_);
                    v___x_2395_ = v___x_2376_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_cache_2371_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2399_,
                        2,
                        v_zetaDeltaFVarIds_2372_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_postponed_2373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_diag_2374_);
                    v___x_2395_ = v_reuseFailAlloc_2399_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2396_ = lean_st_ref_set(v___y_2367_, v___x_2395_);
                v___x_2397_ = crate::leanh::lean_box(0);
                v___x_2398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
                return v___x_2398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(
    mut v_mvarId_2403_: *mut crate::leanh::LeanObject,
    mut v_val_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
        v_mvarId_2403_,
        v_val_2404_,
        v___y_2405_,
    );
    crate::leanh::lean_dec(v___y_2405_);
    return v_res_2407_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_Meta_injectionCore___lam__1___closed__1;
    v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__2_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__2,
    );
    v___x_2414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_Meta_injectionCore___lam__1___closed__5;
    v___x_2419_ = l_Lean_MessageData_ofFormat(v___x_2418_);
    return v___x_2419_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__6_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__6,
    );
    v___x_2421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2420_);
    return v___x_2421_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Meta_injectionCore___lam__1___closed__8;
    v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
    return v___x_2424_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Lean_Meta_injectionCore___lam__1___closed__10;
    v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
    return v___x_2427_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = l_Lean_Meta_injectionCore___lam__1___closed__12;
    v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__14() -> u64 {
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: u64 = 0;
    v___x_2431_ = 1;
    v___x_2432_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Lean_Meta_injectionCore___lam__1___closed__15;
    v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_Meta_injectionCore___lam__1___closed__17;
    v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = l_Lean_Meta_injectionCore___lam__1___closed__22;
    v___x_2446_ = l_Lean_MessageData_ofFormat(v___x_2445_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__23_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__23,
    );
    v___x_2448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2447_);
    return v___x_2448_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lean_Meta_injectionCore___lam__1___closed__27;
    v___x_2453_ = l_Lean_stringToMessageData(v___x_2452_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lean_Meta_injectionCore___lam__1___closed__29;
    v___x_2456_ = l_Lean_stringToMessageData(v___x_2455_);
    return v___x_2456_;
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__1(
    mut v_mvarId_2460_: *mut crate::leanh::LeanObject,
    mut v___x_2461_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2462_: *mut crate::leanh::LeanObject,
    mut v___x_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut v_unused_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_reuseFailAlloc_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_unused_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_a_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_a_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut v___y_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2646_: u8 = 0;
    let mut v_ctxApprox_2647_: u8 = 0;
    let mut v_quasiPatternApprox_2648_: u8 = 0;
    let mut v_constApprox_2649_: u8 = 0;
    let mut v_isDefEqStuckEx_2650_: u8 = 0;
    let mut v_unificationHints_2651_: u8 = 0;
    let mut v_proofIrrelevance_2652_: u8 = 0;
    let mut v_assignSyntheticOpaque_2653_: u8 = 0;
    let mut v_offsetCnstrs_2654_: u8 = 0;
    let mut v_etaStruct_2655_: u8 = 0;
    let mut v_univApprox_2656_: u8 = 0;
    let mut v_iota_2657_: u8 = 0;
    let mut v_beta_2658_: u8 = 0;
    let mut v_proj_2659_: u8 = 0;
    let mut v_zeta_2660_: u8 = 0;
    let mut v_zetaDelta_2661_: u8 = 0;
    let mut v_zetaUnused_2662_: u8 = 0;
    let mut v_zetaHave_2663_: u8 = 0;
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_trackZetaDelta_2667_: u8 = 0;
    let mut v_zetaDeltaSet_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2674_: u8 = 0;
    let mut v_inTypeClassResolution_2675_: u8 = 0;
    let mut v_cacheInferType_2676_: u8 = 0;
    let mut v___x_2677_: u8 = 0;
    let mut v_config_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u64 = 0;
    let mut v___x_2681_: u64 = 0;
    let mut v___x_2682_: u64 = 0;
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    let mut v_key_2685_: u64 = 0;
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_a_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2718_: u8 = 0;
    let mut v_a_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_a_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_reuseFailAlloc_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_type_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_reuseFailAlloc_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2850_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v_a_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_a_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_a_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_2461_);
                crate::leanh::lean_inc(v_mvarId_2460_);
                v___x_2823_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2460_,
                    v___x_2461_,
                    v___y_2464_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                );
                if crate::leanh::lean_obj_tag(v___x_2823_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2823_, 1);
                    crate::leanh::lean_inc(v_fvarId_2462_);
                    v___x_2824_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_2462_,
                        v___y_2464_,
                        v___y_2466_,
                        v___y_2467_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2824_) == 0 {
                        v_a_2825_ = crate::leanh::lean_ctor_get(v___x_2824_, 0);
                        crate::leanh::lean_inc(v_a_2825_);
                        crate::leanh::lean_dec_ref_known(v___x_2824_, 1);
                        v___x_2826_ = l_Lean_LocalDecl_type(v_a_2825_);
                        crate::leanh::lean_dec(v_a_2825_);
                        crate::leanh::lean_inc(v___y_2467_);
                        crate::leanh::lean_inc_ref(v___y_2466_);
                        crate::leanh::lean_inc(v___y_2465_);
                        crate::leanh::lean_inc_ref(v___y_2464_);
                        v___x_2827_ = lean_whnf(
                            v___x_2826_,
                            v___y_2464_,
                            v___y_2465_,
                            v___y_2466_,
                            v___y_2467_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2827_) == 0 {
                            v_a_2828_ = crate::leanh::lean_ctor_get(v___x_2827_, 0);
                            crate::leanh::lean_inc(v_a_2828_);
                            crate::leanh::lean_dec_ref_known(v___x_2827_, 1);
                            crate::leanh::lean_inc(v_fvarId_2462_);
                            v___x_2829_ = l_Lean_mkFVar(v_fvarId_2462_);
                            v___x_2830_ = l_Lean_Meta_injectionCore___lam__1___closed__32;
                            v___x_2831_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_2832_ =
                                l_Lean_Expr_isAppOfArity(v_a_2828_, v___x_2830_, v___x_2831_);
                            if v___x_2832_ == 0 {
                                v_type_2738_ = v_a_2828_;
                                v_prf_2739_ = v___x_2829_;
                                v___y_2740_ = v___y_2464_;
                                v___y_2741_ = v___y_2465_;
                                v___y_2742_ = v___y_2466_;
                                v___y_2743_ = v___y_2467_;
                                state = 38;
                                continue;
                            } else {
                                v___x_2833_ = l_Lean_Expr_appFn_x21(v_a_2828_);
                                v___x_2834_ = l_Lean_Expr_appFn_x21(v___x_2833_);
                                v___x_2835_ = l_Lean_Expr_appFn_x21(v___x_2834_);
                                v___x_2836_ = l_Lean_Expr_appArg_x21(v___x_2835_);
                                crate::leanh::lean_dec_ref(v___x_2835_);
                                v___x_2837_ = l_Lean_Expr_appArg_x21(v___x_2833_);
                                crate::leanh::lean_dec_ref(v___x_2833_);
                                v___x_2838_ = l_Lean_Meta_isExprDefEq(
                                    v___x_2836_,
                                    v___x_2837_,
                                    v___y_2464_,
                                    v___y_2465_,
                                    v___y_2466_,
                                    v___y_2467_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2838_) == 0 {
                                    v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                                    crate::leanh::lean_inc(v_a_2839_);
                                    crate::leanh::lean_dec_ref_known(v___x_2838_, 1);
                                    v___x_2840_ = (crate::leanh::lean_unbox(v_a_2839_) as u8);
                                    crate::leanh::lean_dec(v_a_2839_);
                                    if v___x_2840_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2834_);
                                        v_type_2738_ = v_a_2828_;
                                        v_prf_2739_ = v___x_2829_;
                                        v___y_2740_ = v___y_2464_;
                                        v___y_2741_ = v___y_2465_;
                                        v___y_2742_ = v___y_2466_;
                                        v___y_2743_ = v___y_2467_;
                                        state = 38;
                                        continue;
                                    } else {
                                        v___x_2841_ = l_Lean_Expr_appArg_x21(v___x_2834_);
                                        crate::leanh::lean_dec_ref(v___x_2834_);
                                        v___x_2842_ = l_Lean_Expr_appArg_x21(v_a_2828_);
                                        crate::leanh::lean_dec(v_a_2828_);
                                        v___x_2843_ = l_Lean_Meta_mkEq(
                                            v___x_2841_,
                                            v___x_2842_,
                                            v___y_2464_,
                                            v___y_2465_,
                                            v___y_2466_,
                                            v___y_2467_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2843_) == 0 {
                                            v_a_2844_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                                            crate::leanh::lean_inc(v_a_2844_);
                                            crate::leanh::lean_dec_ref_known(v___x_2843_, 1);
                                            v___x_2845_ = l_Lean_Meta_mkEqOfHEq(
                                                v___x_2829_,
                                                v___x_2832_,
                                                v___y_2464_,
                                                v___y_2465_,
                                                v___y_2466_,
                                                v___y_2467_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2845_) == 0 {
                                                v_a_2846_ =
                                                    crate::leanh::lean_ctor_get(v___x_2845_, 0);
                                                crate::leanh::lean_inc(v_a_2846_);
                                                crate::leanh::lean_dec_ref_known(v___x_2845_, 1);
                                                v_type_2738_ = v_a_2844_;
                                                v_prf_2739_ = v_a_2846_;
                                                v___y_2740_ = v___y_2464_;
                                                v___y_2741_ = v___y_2465_;
                                                v___y_2742_ = v___y_2466_;
                                                v___y_2743_ = v___y_2467_;
                                                state = 38;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_a_2844_);
                                                crate::leanh::lean_dec(v___y_2467_);
                                                crate::leanh::lean_dec_ref(v___y_2466_);
                                                crate::leanh::lean_dec(v___y_2465_);
                                                crate::leanh::lean_dec_ref(v___y_2464_);
                                                crate::leanh::lean_dec_ref(v___x_2463_);
                                                crate::leanh::lean_dec(v_fvarId_2462_);
                                                crate::leanh::lean_dec(v___x_2461_);
                                                crate::leanh::lean_dec(v_mvarId_2460_);
                                                v_a_2847_ =
                                                    crate::leanh::lean_ctor_get(v___x_2845_, 0);
                                                v_isSharedCheck_2854_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2845_))
                                                        as u8;
                                                if v_isSharedCheck_2854_ == 0 {
                                                    v___x_2849_ = v___x_2845_;
                                                    v_isShared_2850_ = v_isSharedCheck_2854_;
                                                    state = 51;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2847_);
                                                    crate::leanh::lean_dec(v___x_2845_);
                                                    v___x_2849_ = crate::leanh::lean_box(0);
                                                    v_isShared_2850_ = v_isSharedCheck_2854_;
                                                    state = 51;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2829_);
                                            crate::leanh::lean_dec(v___y_2467_);
                                            crate::leanh::lean_dec_ref(v___y_2466_);
                                            crate::leanh::lean_dec(v___y_2465_);
                                            crate::leanh::lean_dec_ref(v___y_2464_);
                                            crate::leanh::lean_dec_ref(v___x_2463_);
                                            crate::leanh::lean_dec(v_fvarId_2462_);
                                            crate::leanh::lean_dec(v___x_2461_);
                                            crate::leanh::lean_dec(v_mvarId_2460_);
                                            v_a_2855_ = crate::leanh::lean_ctor_get(v___x_2843_, 0);
                                            v_isSharedCheck_2862_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2843_))
                                                    as u8;
                                            if v_isSharedCheck_2862_ == 0 {
                                                v___x_2857_ = v___x_2843_;
                                                v_isShared_2858_ = v_isSharedCheck_2862_;
                                                state = 53;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2855_);
                                                crate::leanh::lean_dec(v___x_2843_);
                                                v___x_2857_ = crate::leanh::lean_box(0);
                                                v_isShared_2858_ = v_isSharedCheck_2862_;
                                                state = 53;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2834_);
                                    crate::leanh::lean_dec_ref(v___x_2829_);
                                    crate::leanh::lean_dec(v_a_2828_);
                                    crate::leanh::lean_dec(v___y_2467_);
                                    crate::leanh::lean_dec_ref(v___y_2466_);
                                    crate::leanh::lean_dec(v___y_2465_);
                                    crate::leanh::lean_dec_ref(v___y_2464_);
                                    crate::leanh::lean_dec_ref(v___x_2463_);
                                    crate::leanh::lean_dec(v_fvarId_2462_);
                                    crate::leanh::lean_dec(v___x_2461_);
                                    crate::leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2863_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                                    v_isSharedCheck_2870_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2838_)) as u8;
                                    if v_isSharedCheck_2870_ == 0 {
                                        v___x_2865_ = v___x_2838_;
                                        v_isShared_2866_ = v_isSharedCheck_2870_;
                                        state = 55;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2863_);
                                        crate::leanh::lean_dec(v___x_2838_);
                                        v___x_2865_ = crate::leanh::lean_box(0);
                                        v_isShared_2866_ = v_isSharedCheck_2870_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_2467_);
                            crate::leanh::lean_dec_ref(v___y_2466_);
                            crate::leanh::lean_dec(v___y_2465_);
                            crate::leanh::lean_dec_ref(v___y_2464_);
                            crate::leanh::lean_dec_ref(v___x_2463_);
                            crate::leanh::lean_dec(v_fvarId_2462_);
                            crate::leanh::lean_dec(v___x_2461_);
                            crate::leanh::lean_dec(v_mvarId_2460_);
                            v_a_2871_ = crate::leanh::lean_ctor_get(v___x_2827_, 0);
                            v_isSharedCheck_2878_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2827_)) as u8;
                            if v_isSharedCheck_2878_ == 0 {
                                v___x_2873_ = v___x_2827_;
                                v_isShared_2874_ = v_isSharedCheck_2878_;
                                state = 57;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2871_);
                                crate::leanh::lean_dec(v___x_2827_);
                                v___x_2873_ = crate::leanh::lean_box(0);
                                v_isShared_2874_ = v_isSharedCheck_2878_;
                                state = 57;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2467_);
                        crate::leanh::lean_dec_ref(v___y_2466_);
                        crate::leanh::lean_dec(v___y_2465_);
                        crate::leanh::lean_dec_ref(v___y_2464_);
                        crate::leanh::lean_dec_ref(v___x_2463_);
                        crate::leanh::lean_dec(v_fvarId_2462_);
                        crate::leanh::lean_dec(v___x_2461_);
                        crate::leanh::lean_dec(v_mvarId_2460_);
                        v_a_2879_ = crate::leanh::lean_ctor_get(v___x_2824_, 0);
                        v_isSharedCheck_2886_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2824_)) as u8;
                        if v_isSharedCheck_2886_ == 0 {
                            v___x_2881_ = v___x_2824_;
                            v_isShared_2882_ = v_isSharedCheck_2886_;
                            state = 59;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2879_);
                            crate::leanh::lean_dec(v___x_2824_);
                            v___x_2881_ = crate::leanh::lean_box(0);
                            v_isShared_2882_ = v_isSharedCheck_2886_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2467_);
                    crate::leanh::lean_dec_ref(v___y_2466_);
                    crate::leanh::lean_dec(v___y_2465_);
                    crate::leanh::lean_dec_ref(v___y_2464_);
                    crate::leanh::lean_dec_ref(v___x_2463_);
                    crate::leanh::lean_dec(v_fvarId_2462_);
                    crate::leanh::lean_dec(v___x_2461_);
                    crate::leanh::lean_dec(v_mvarId_2460_);
                    v_a_2887_ = crate::leanh::lean_ctor_get(v___x_2823_, 0);
                    v_isSharedCheck_2894_ = (!crate::leanh::lean_is_exclusive(v___x_2823_)) as u8;
                    if v_isSharedCheck_2894_ == 0 {
                        v___x_2889_ = v___x_2823_;
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 61;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2887_);
                        crate::leanh::lean_dec(v___x_2823_);
                        v___x_2889_ = crate::leanh::lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 61;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2474_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__3_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__3,
                );
                v___x_2475_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_2461_,
                    v_mvarId_2460_,
                    v___x_2474_,
                    v___y_2470_,
                    v___y_2471_,
                    v___y_2472_,
                    v___y_2473_,
                );
                crate::leanh::lean_dec(v___y_2473_);
                crate::leanh::lean_dec_ref(v___y_2472_);
                crate::leanh::lean_dec(v___y_2471_);
                crate::leanh::lean_dec_ref(v___y_2470_);
                return v___x_2475_;
            }
            2 => {
                v___x_2481_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__7_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__7,
                );
                v___x_2482_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_2461_,
                    v_mvarId_2460_,
                    v___x_2481_,
                    v___y_2477_,
                    v___y_2478_,
                    v___y_2479_,
                    v___y_2480_,
                );
                crate::leanh::lean_dec(v___y_2480_);
                crate::leanh::lean_dec_ref(v___y_2479_);
                crate::leanh::lean_dec(v___y_2478_);
                crate::leanh::lean_dec_ref(v___y_2477_);
                return v___x_2482_;
            }
            3 => {
                v___x_2486_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2486_, 0, v___y_2485_);
                crate::leanh::lean_ctor_set(v___x_2486_, 1, v___y_2484_);
                v___x_2487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2487_, 0, v___x_2486_);
                return v___x_2487_;
            }
            4 => {
                v_toConstantVal_2498_ = crate::leanh::lean_ctor_get(v___y_2493_, 0);
                v_toConstantVal_2499_ = crate::leanh::lean_ctor_get(v___y_2492_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_2499_);
                crate::leanh::lean_dec_ref(v___y_2492_);
                v_numFields_2500_ = crate::leanh::lean_ctor_get(v___y_2493_, 4);
                crate::leanh::lean_inc(v_numFields_2500_);
                v_name_2501_ = crate::leanh::lean_ctor_get(v_toConstantVal_2498_, 0);
                v_name_2502_ = crate::leanh::lean_ctor_get(v_toConstantVal_2499_, 0);
                crate::leanh::lean_inc(v_name_2502_);
                crate::leanh::lean_dec_ref(v_toConstantVal_2499_);
                v___x_2503_ = lean_name_eq(v_name_2501_, v_name_2502_);
                crate::leanh::lean_dec(v_name_2502_);
                if v___x_2503_ == 0 {
                    crate::leanh::lean_dec(v_numFields_2500_);
                    crate::leanh::lean_dec(v___y_2497_);
                    crate::leanh::lean_dec_ref(v___y_2496_);
                    crate::leanh::lean_dec_ref(v___y_2494_);
                    crate::leanh::lean_dec_ref(v___y_2493_);
                    crate::leanh::lean_dec(v___y_2491_);
                    crate::leanh::lean_dec_ref(v___y_2490_);
                    crate::leanh::lean_dec(v_fvarId_2462_);
                    crate::leanh::lean_dec(v___x_2461_);
                    v___x_2504_ =
                        l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
                            v_mvarId_2460_,
                            v___y_2489_,
                            v___y_2495_,
                        );
                    crate::leanh::lean_dec(v___y_2495_);
                    v_isSharedCheck_2512_ = (!crate::leanh::lean_is_exclusive(v___x_2504_)) as u8;
                    if v_isSharedCheck_2512_ == 0 {
                        v_unused_2513_ = crate::leanh::lean_ctor_get(v___x_2504_, 0);
                        crate::leanh::lean_dec(v_unused_2513_);
                        v___x_2506_ = v___x_2504_;
                        v_isShared_2507_ = v_isSharedCheck_2512_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2504_);
                        v___x_2506_ = crate::leanh::lean_box(0);
                        v_isShared_2507_ = v_isSharedCheck_2512_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v___y_2497_);
                    crate::leanh::lean_inc_ref(v___y_2496_);
                    crate::leanh::lean_inc(v___y_2495_);
                    crate::leanh::lean_inc_ref(v___y_2494_);
                    crate::leanh::lean_inc_ref(v___y_2489_);
                    v___x_2514_ = lean_infer_type(
                        v___y_2489_,
                        v___y_2494_,
                        v___y_2495_,
                        v___y_2496_,
                        v___y_2497_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2514_) == 0 {
                        v_a_2515_ = crate::leanh::lean_ctor_get(v___x_2514_, 0);
                        crate::leanh::lean_inc(v_a_2515_);
                        crate::leanh::lean_dec_ref_known(v___x_2514_, 1);
                        v___x_2516_ = l_Lean_Meta_whnfD(
                            v_a_2515_,
                            v___y_2494_,
                            v___y_2495_,
                            v___y_2496_,
                            v___y_2497_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2516_) == 0 {
                            v_a_2517_ = crate::leanh::lean_ctor_get(v___x_2516_, 0);
                            crate::leanh::lean_inc(v_a_2517_);
                            crate::leanh::lean_dec_ref_known(v___x_2516_, 1);
                            if crate::leanh::lean_obj_tag(v_a_2517_) == 7 {
                                crate::leanh::lean_dec_ref(v___y_2490_);
                                crate::leanh::lean_dec(v___x_2461_);
                                v_binderType_2518_ = crate::leanh::lean_ctor_get(v_a_2517_, 1);
                                crate::leanh::lean_inc_ref(v_binderType_2518_);
                                crate::leanh::lean_dec_ref_known(v_a_2517_, 3);
                                crate::leanh::lean_inc(v_mvarId_2460_);
                                v___x_2519_ = l_Lean_MVarId_getTag(
                                    v_mvarId_2460_,
                                    v___y_2494_,
                                    v___y_2495_,
                                    v___y_2496_,
                                    v___y_2497_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2519_) == 0 {
                                    v_a_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                    crate::leanh::lean_inc(v_a_2520_);
                                    crate::leanh::lean_dec_ref_known(v___x_2519_, 1);
                                    v___x_2521_ = l_Lean_Expr_headBeta(v_binderType_2518_);
                                    v___x_2522_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                        v___x_2521_,
                                        v_a_2520_,
                                        v___y_2494_,
                                        v___y_2495_,
                                        v___y_2496_,
                                        v___y_2497_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2522_) == 0 {
                                        v_a_2523_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                                        crate::leanh::lean_inc_n(v_a_2523_, 2);
                                        crate::leanh::lean_dec_ref_known(v___x_2522_, 1);
                                        v___x_2524_ =
                                            l_Lean_Expr_app___override(v___y_2489_, v_a_2523_);
                                        v___x_2525_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_2460_, v___x_2524_, v___y_2495_);
                                        v_isSharedCheck_2577_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2525_)) as u8;
                                        if v_isSharedCheck_2577_ == 0 {
                                            v_unused_2578_ =
                                                crate::leanh::lean_ctor_get(v___x_2525_, 0);
                                            crate::leanh::lean_dec(v_unused_2578_);
                                            v___x_2527_ = v___x_2525_;
                                            v_isShared_2528_ = v_isSharedCheck_2577_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_2525_);
                                            v___x_2527_ = crate::leanh::lean_box(0);
                                            v_isShared_2528_ = v_isSharedCheck_2577_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_numFields_2500_);
                                        crate::leanh::lean_dec(v___y_2497_);
                                        crate::leanh::lean_dec_ref(v___y_2496_);
                                        crate::leanh::lean_dec(v___y_2495_);
                                        crate::leanh::lean_dec_ref(v___y_2494_);
                                        crate::leanh::lean_dec_ref(v___y_2493_);
                                        crate::leanh::lean_dec(v___y_2491_);
                                        crate::leanh::lean_dec_ref(v___y_2489_);
                                        crate::leanh::lean_dec(v_fvarId_2462_);
                                        crate::leanh::lean_dec(v_mvarId_2460_);
                                        v_a_2579_ = crate::leanh::lean_ctor_get(v___x_2522_, 0);
                                        v_isSharedCheck_2586_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2522_)) as u8;
                                        if v_isSharedCheck_2586_ == 0 {
                                            v___x_2581_ = v___x_2522_;
                                            v_isShared_2582_ = v_isSharedCheck_2586_;
                                            state = 15;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2579_);
                                            crate::leanh::lean_dec(v___x_2522_);
                                            v___x_2581_ = crate::leanh::lean_box(0);
                                            v_isShared_2582_ = v_isSharedCheck_2586_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_binderType_2518_);
                                    crate::leanh::lean_dec(v_numFields_2500_);
                                    crate::leanh::lean_dec(v___y_2497_);
                                    crate::leanh::lean_dec_ref(v___y_2496_);
                                    crate::leanh::lean_dec(v___y_2495_);
                                    crate::leanh::lean_dec_ref(v___y_2494_);
                                    crate::leanh::lean_dec_ref(v___y_2493_);
                                    crate::leanh::lean_dec(v___y_2491_);
                                    crate::leanh::lean_dec_ref(v___y_2489_);
                                    crate::leanh::lean_dec(v_fvarId_2462_);
                                    crate::leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2587_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                                    v_isSharedCheck_2594_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2519_)) as u8;
                                    if v_isSharedCheck_2594_ == 0 {
                                        v___x_2589_ = v___x_2519_;
                                        v_isShared_2590_ = v_isSharedCheck_2594_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2587_);
                                        crate::leanh::lean_dec(v___x_2519_);
                                        v___x_2589_ = crate::leanh::lean_box(0);
                                        v_isShared_2590_ = v_isSharedCheck_2594_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_numFields_2500_);
                                crate::leanh::lean_dec_ref(v___y_2493_);
                                crate::leanh::lean_dec_ref(v___y_2489_);
                                crate::leanh::lean_dec(v_fvarId_2462_);
                                crate::leanh::lean_inc(v___y_2497_);
                                crate::leanh::lean_inc_ref(v___y_2496_);
                                crate::leanh::lean_inc(v___y_2495_);
                                crate::leanh::lean_inc_ref(v___y_2494_);
                                v___x_2595_ = crate::leanh::lean_apply_5(
                                    v___y_2490_,
                                    v___y_2494_,
                                    v___y_2495_,
                                    v___y_2496_,
                                    v___y_2497_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_2595_) == 0 {
                                    v_a_2596_ = crate::leanh::lean_ctor_get(v___x_2595_, 0);
                                    crate::leanh::lean_inc(v_a_2596_);
                                    crate::leanh::lean_dec_ref_known(v___x_2595_, 1);
                                    v___x_2597_ = (crate::leanh::lean_unbox(v_a_2596_) as u8);
                                    crate::leanh::lean_dec(v_a_2596_);
                                    if v___x_2597_ == 0 {
                                        crate::leanh::lean_dec(v_a_2517_);
                                        crate::leanh::lean_dec(v___y_2491_);
                                        v___y_2470_ = v___y_2494_;
                                        v___y_2471_ = v___y_2495_;
                                        v___y_2472_ = v___y_2496_;
                                        v___y_2473_ = v___y_2497_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2598_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__13_once), _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
                                        v___x_2599_ = l_Lean_indentExpr(v_a_2517_);
                                        v___x_2600_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                                        crate::leanh::lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                                        v___x_2601_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_2491_, v___x_2600_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
                                        if crate::leanh::lean_obj_tag(v___x_2601_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_2601_, 1);
                                            v___y_2470_ = v___y_2494_;
                                            v___y_2471_ = v___y_2495_;
                                            v___y_2472_ = v___y_2496_;
                                            v___y_2473_ = v___y_2497_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___y_2497_);
                                            crate::leanh::lean_dec_ref(v___y_2496_);
                                            crate::leanh::lean_dec(v___y_2495_);
                                            crate::leanh::lean_dec_ref(v___y_2494_);
                                            crate::leanh::lean_dec(v___x_2461_);
                                            crate::leanh::lean_dec(v_mvarId_2460_);
                                            v_a_2602_ = crate::leanh::lean_ctor_get(v___x_2601_, 0);
                                            v_isSharedCheck_2609_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2601_))
                                                    as u8;
                                            if v_isSharedCheck_2609_ == 0 {
                                                v___x_2604_ = v___x_2601_;
                                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                                state = 19;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2602_);
                                                crate::leanh::lean_dec(v___x_2601_);
                                                v___x_2604_ = crate::leanh::lean_box(0);
                                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                                state = 19;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2517_);
                                    crate::leanh::lean_dec(v___y_2497_);
                                    crate::leanh::lean_dec_ref(v___y_2496_);
                                    crate::leanh::lean_dec(v___y_2495_);
                                    crate::leanh::lean_dec_ref(v___y_2494_);
                                    crate::leanh::lean_dec(v___y_2491_);
                                    crate::leanh::lean_dec(v___x_2461_);
                                    crate::leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2610_ = crate::leanh::lean_ctor_get(v___x_2595_, 0);
                                    v_isSharedCheck_2617_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2595_)) as u8;
                                    if v_isSharedCheck_2617_ == 0 {
                                        v___x_2612_ = v___x_2595_;
                                        v_isShared_2613_ = v_isSharedCheck_2617_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2610_);
                                        crate::leanh::lean_dec(v___x_2595_);
                                        v___x_2612_ = crate::leanh::lean_box(0);
                                        v_isShared_2613_ = v_isSharedCheck_2617_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_numFields_2500_);
                            crate::leanh::lean_dec(v___y_2497_);
                            crate::leanh::lean_dec_ref(v___y_2496_);
                            crate::leanh::lean_dec(v___y_2495_);
                            crate::leanh::lean_dec_ref(v___y_2494_);
                            crate::leanh::lean_dec_ref(v___y_2493_);
                            crate::leanh::lean_dec(v___y_2491_);
                            crate::leanh::lean_dec_ref(v___y_2490_);
                            crate::leanh::lean_dec_ref(v___y_2489_);
                            crate::leanh::lean_dec(v_fvarId_2462_);
                            crate::leanh::lean_dec(v___x_2461_);
                            crate::leanh::lean_dec(v_mvarId_2460_);
                            v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2516_, 0);
                            v_isSharedCheck_2625_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2516_)) as u8;
                            if v_isSharedCheck_2625_ == 0 {
                                v___x_2620_ = v___x_2516_;
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2618_);
                                crate::leanh::lean_dec(v___x_2516_);
                                v___x_2620_ = crate::leanh::lean_box(0);
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_numFields_2500_);
                        crate::leanh::lean_dec(v___y_2497_);
                        crate::leanh::lean_dec_ref(v___y_2496_);
                        crate::leanh::lean_dec(v___y_2495_);
                        crate::leanh::lean_dec_ref(v___y_2494_);
                        crate::leanh::lean_dec_ref(v___y_2493_);
                        crate::leanh::lean_dec(v___y_2491_);
                        crate::leanh::lean_dec_ref(v___y_2490_);
                        crate::leanh::lean_dec_ref(v___y_2489_);
                        crate::leanh::lean_dec(v_fvarId_2462_);
                        crate::leanh::lean_dec(v___x_2461_);
                        crate::leanh::lean_dec(v_mvarId_2460_);
                        v_a_2626_ = crate::leanh::lean_ctor_get(v___x_2514_, 0);
                        v_isSharedCheck_2633_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2514_)) as u8;
                        if v_isSharedCheck_2633_ == 0 {
                            v___x_2628_ = v___x_2514_;
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2626_);
                            crate::leanh::lean_dec(v___x_2514_);
                            v___x_2628_ = crate::leanh::lean_box(0);
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_2508_ = crate::leanh::lean_box(0);
                if v_isShared_2507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2508_);
                    v___x_2510_ = v___x_2506_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
                    v___x_2510_ = v_reuseFailAlloc_2511_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2510_;
            }
            7 => {
                v___x_2529_ = l_Lean_Expr_mvarId_x21(v_a_2523_);
                crate::leanh::lean_dec(v_a_2523_);
                v___x_2530_ = l_Lean_MVarId_tryClear(
                    v___x_2529_,
                    v_fvarId_2462_,
                    v___y_2494_,
                    v___y_2495_,
                    v___y_2496_,
                    v___y_2497_,
                );
                if crate::leanh::lean_obj_tag(v___x_2530_) == 0 {
                    v_a_2531_ = crate::leanh::lean_ctor_get(v___x_2530_, 0);
                    crate::leanh::lean_inc(v_a_2531_);
                    crate::leanh::lean_dec_ref_known(v___x_2530_, 1);
                    v___x_2532_ = l_Lean_Meta_getCtorNumPropFields(
                        v___y_2493_,
                        v___y_2494_,
                        v___y_2495_,
                        v___y_2496_,
                        v___y_2497_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2532_) == 0 {
                        v_options_2533_ = crate::leanh::lean_ctor_get(v___y_2496_, 2);
                        v_a_2534_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                        crate::leanh::lean_inc(v_a_2534_);
                        crate::leanh::lean_dec_ref_known(v___x_2532_, 1);
                        v_inheritedTraceOptions_2535_ =
                            crate::leanh::lean_ctor_get(v___y_2496_, 13);
                        v_hasTrace_2536_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_2533_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        v___x_2537_ = lean_nat_sub(v_numFields_2500_, v_a_2534_);
                        crate::leanh::lean_dec(v_a_2534_);
                        crate::leanh::lean_dec(v_numFields_2500_);
                        if v_hasTrace_2536_ == 0 {
                            crate::leanh::lean_del_object(v___x_2527_);
                            crate::leanh::lean_dec(v___y_2497_);
                            crate::leanh::lean_dec_ref(v___y_2496_);
                            crate::leanh::lean_dec(v___y_2495_);
                            crate::leanh::lean_dec_ref(v___y_2494_);
                            crate::leanh::lean_dec(v___y_2491_);
                            v___y_2484_ = v___x_2537_;
                            v___y_2485_ = v_a_2531_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2538_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
                            crate::leanh::lean_inc(v___y_2491_);
                            v___x_2539_ = l_Lean_Name_append(v___x_2538_, v___y_2491_);
                            v___x_2540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2535_,
                                v_options_2533_,
                                v___x_2539_,
                            );
                            crate::leanh::lean_dec(v___x_2539_);
                            if v___x_2540_ == 0 {
                                crate::leanh::lean_del_object(v___x_2527_);
                                crate::leanh::lean_dec(v___y_2497_);
                                crate::leanh::lean_dec_ref(v___y_2496_);
                                crate::leanh::lean_dec(v___y_2495_);
                                crate::leanh::lean_dec_ref(v___y_2494_);
                                crate::leanh::lean_dec(v___y_2491_);
                                v___y_2484_ = v___x_2537_;
                                v___y_2485_ = v_a_2531_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2541_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__9
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__9_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__9,
                                );
                                crate::leanh::lean_inc(v___x_2537_);
                                v___x_2542_ = l_Nat_reprFast(v___x_2537_);
                                if v_isShared_2528_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_2527_, 3);
                                    crate::leanh::lean_ctor_set(v___x_2527_, 0, v___x_2542_);
                                    v___x_2544_ = v___x_2527_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2560_ =
                                        crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2560_,
                                        0,
                                        v___x_2542_,
                                    );
                                    v___x_2544_ = v_reuseFailAlloc_2560_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2531_);
                        crate::leanh::lean_del_object(v___x_2527_);
                        crate::leanh::lean_dec(v_numFields_2500_);
                        crate::leanh::lean_dec(v___y_2497_);
                        crate::leanh::lean_dec_ref(v___y_2496_);
                        crate::leanh::lean_dec(v___y_2495_);
                        crate::leanh::lean_dec_ref(v___y_2494_);
                        crate::leanh::lean_dec(v___y_2491_);
                        v_a_2561_ = crate::leanh::lean_ctor_get(v___x_2532_, 0);
                        v_isSharedCheck_2568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2532_)) as u8;
                        if v_isSharedCheck_2568_ == 0 {
                            v___x_2563_ = v___x_2532_;
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2561_);
                            crate::leanh::lean_dec(v___x_2532_);
                            v___x_2563_ = crate::leanh::lean_box(0);
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2527_);
                    crate::leanh::lean_dec(v_numFields_2500_);
                    crate::leanh::lean_dec(v___y_2497_);
                    crate::leanh::lean_dec_ref(v___y_2496_);
                    crate::leanh::lean_dec(v___y_2495_);
                    crate::leanh::lean_dec_ref(v___y_2494_);
                    crate::leanh::lean_dec_ref(v___y_2493_);
                    crate::leanh::lean_dec(v___y_2491_);
                    v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2530_, 0);
                    v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v___x_2530_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2530_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2569_);
                        crate::leanh::lean_dec(v___x_2530_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2545_ = l_Lean_MessageData_ofFormat(v___x_2544_);
                v___x_2546_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2541_);
                crate::leanh::lean_ctor_set(v___x_2546_, 1, v___x_2545_);
                v___x_2547_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__11_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__11,
                );
                v___x_2548_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2548_, 0, v___x_2546_);
                crate::leanh::lean_ctor_set(v___x_2548_, 1, v___x_2547_);
                crate::leanh::lean_inc(v_a_2531_);
                v___x_2549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2549_, 0, v_a_2531_);
                v___x_2550_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2550_, 0, v___x_2548_);
                crate::leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
                v___x_2551_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                    v___y_2491_,
                    v___x_2550_,
                    v___y_2494_,
                    v___y_2495_,
                    v___y_2496_,
                    v___y_2497_,
                );
                crate::leanh::lean_dec(v___y_2497_);
                crate::leanh::lean_dec_ref(v___y_2496_);
                crate::leanh::lean_dec(v___y_2495_);
                crate::leanh::lean_dec_ref(v___y_2494_);
                if crate::leanh::lean_obj_tag(v___x_2551_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2551_, 1);
                    v___y_2484_ = v___x_2537_;
                    v___y_2485_ = v_a_2531_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2537_);
                    crate::leanh::lean_dec(v_a_2531_);
                    v_a_2552_ = crate::leanh::lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2559_ = (!crate::leanh::lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2554_ = v___x_2551_;
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2552_);
                        crate::leanh::lean_dec(v___x_2551_);
                        v___x_2554_ = crate::leanh::lean_box(0);
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2555_ == 0 {
                    v___x_2557_ = v___x_2554_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2557_;
            }
            11 => {
                if v_isShared_2564_ == 0 {
                    v___x_2566_ = v___x_2563_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2566_;
            }
            13 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2574_;
            }
            15 => {
                if v_isShared_2582_ == 0 {
                    v___x_2584_ = v___x_2581_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2584_;
            }
            17 => {
                if v_isShared_2590_ == 0 {
                    v___x_2592_ = v___x_2589_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
                    v___x_2592_ = v_reuseFailAlloc_2593_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2592_;
            }
            19 => {
                if v_isShared_2605_ == 0 {
                    v___x_2607_ = v___x_2604_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
                    v___x_2607_ = v_reuseFailAlloc_2608_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2607_;
            }
            21 => {
                if v_isShared_2613_ == 0 {
                    v___x_2615_ = v___x_2612_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
                    v___x_2615_ = v_reuseFailAlloc_2616_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2615_;
            }
            23 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2623_;
            }
            25 => {
                if v_isShared_2629_ == 0 {
                    v___x_2631_ = v___x_2628_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2631_;
            }
            27 => {
                v___x_2645_ = l_Lean_Meta_Context_config(v___y_2641_);
                v_foApprox_2646_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 0 as u32);
                v_ctxApprox_2647_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 1 as u32);
                v_quasiPatternApprox_2648_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2645_, 2 as u32);
                v_constApprox_2649_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 3 as u32);
                v_isDefEqStuckEx_2650_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 4 as u32);
                v_unificationHints_2651_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 5 as u32);
                v_proofIrrelevance_2652_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 6 as u32);
                v_assignSyntheticOpaque_2653_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2645_, 7 as u32);
                v_offsetCnstrs_2654_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 8 as u32);
                v_etaStruct_2655_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 10 as u32);
                v_univApprox_2656_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 11 as u32);
                v_iota_2657_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 12 as u32);
                v_beta_2658_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 13 as u32);
                v_proj_2659_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 14 as u32);
                v_zeta_2660_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 15 as u32);
                v_zetaDelta_2661_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 16 as u32);
                v_zetaUnused_2662_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 17 as u32);
                v_zetaHave_2663_ = crate::leanh::lean_ctor_get_uint8(v___x_2645_, 18 as u32);
                v_isSharedCheck_2736_ = (!crate::leanh::lean_is_exclusive(v___x_2645_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v___x_2665_ = v___x_2645_;
                    v_isShared_2666_ = v_isSharedCheck_2736_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2645_);
                    v___x_2665_ = crate::leanh::lean_box(0);
                    v_isShared_2666_ = v_isSharedCheck_2736_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_trackZetaDelta_2667_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2668_ = crate::leanh::lean_ctor_get(v___y_2641_, 1);
                v_lctx_2669_ = crate::leanh::lean_ctor_get(v___y_2641_, 2);
                v_localInstances_2670_ = crate::leanh::lean_ctor_get(v___y_2641_, 3);
                v_defEqCtx_x3f_2671_ = crate::leanh::lean_ctor_get(v___y_2641_, 4);
                v_synthPendingDepth_2672_ = crate::leanh::lean_ctor_get(v___y_2641_, 5);
                v_canUnfold_x3f_2673_ = crate::leanh::lean_ctor_get(v___y_2641_, 6);
                v_univApprox_2674_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2675_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2676_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2677_ = 1;
                if v_isShared_2666_ == 0 {
                    v_config_2679_ = v___x_2665_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        0 as u32,
                        v_foApprox_2646_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        1 as u32,
                        v_ctxApprox_2647_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        2 as u32,
                        v_quasiPatternApprox_2648_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        3 as u32,
                        v_constApprox_2649_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        4 as u32,
                        v_isDefEqStuckEx_2650_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        5 as u32,
                        v_unificationHints_2651_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        6 as u32,
                        v_proofIrrelevance_2652_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        7 as u32,
                        v_assignSyntheticOpaque_2653_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        8 as u32,
                        v_offsetCnstrs_2654_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        10 as u32,
                        v_etaStruct_2655_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        11 as u32,
                        v_univApprox_2656_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        12 as u32,
                        v_iota_2657_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        13 as u32,
                        v_beta_2658_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        14 as u32,
                        v_proj_2659_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        15 as u32,
                        v_zeta_2660_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        16 as u32,
                        v_zetaDelta_2661_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        17 as u32,
                        v_zetaUnused_2662_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        18 as u32,
                        v_zetaHave_2663_,
                    );
                    v_config_2679_ = v_reuseFailAlloc_2735_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2679_, 9 as u32, v___x_2677_);
                v___x_2680_ = l_Lean_Meta_Context_configKey(v___y_2641_);
                v___x_2681_ = 3u64;
                v___x_2682_ = lean_uint64_shift_right(v___x_2680_, v___x_2681_);
                v___x_2683_ = lean_uint64_shift_left(v___x_2682_, v___x_2681_);
                v___x_2684_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__14_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__14,
                );
                v_key_2685_ = lean_uint64_lor(v___x_2683_, v___x_2684_);
                v___x_2686_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2686_, 0, v_config_2679_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2686_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2685_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2673_);
                crate::leanh::lean_inc(v_synthPendingDepth_2672_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2671_);
                crate::leanh::lean_inc_ref(v_localInstances_2670_);
                crate::leanh::lean_inc_ref(v_lctx_2669_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2668_);
                v___x_2687_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2686_);
                crate::leanh::lean_ctor_set(v___x_2687_, 1, v_zetaDeltaSet_2668_);
                crate::leanh::lean_ctor_set(v___x_2687_, 2, v_lctx_2669_);
                crate::leanh::lean_ctor_set(v___x_2687_, 3, v_localInstances_2670_);
                crate::leanh::lean_ctor_set(v___x_2687_, 4, v_defEqCtx_x3f_2671_);
                crate::leanh::lean_ctor_set(v___x_2687_, 5, v_synthPendingDepth_2672_);
                crate::leanh::lean_ctor_set(v___x_2687_, 6, v_canUnfold_x3f_2673_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2667_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2674_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2675_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2676_,
                );
                v___x_2688_ = l_Lean_Meta_mkNoConfusion(
                    v___y_2636_,
                    v___y_2638_,
                    v___x_2687_,
                    v___y_2642_,
                    v___y_2643_,
                    v___y_2644_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2687_, 7);
                if crate::leanh::lean_obj_tag(v___x_2688_) == 0 {
                    v_a_2689_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                    crate::leanh::lean_inc(v_a_2689_);
                    crate::leanh::lean_dec_ref_known(v___x_2688_, 1);
                    crate::leanh::lean_inc_ref(v___y_2635_);
                    crate::leanh::lean_inc(v___y_2644_);
                    crate::leanh::lean_inc_ref(v___y_2643_);
                    crate::leanh::lean_inc(v___y_2642_);
                    crate::leanh::lean_inc_ref(v___y_2641_);
                    v___x_2690_ = crate::leanh::lean_apply_5(
                        v___y_2635_,
                        v___y_2641_,
                        v___y_2642_,
                        v___y_2643_,
                        v___y_2644_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                        crate::leanh::lean_inc(v_a_2691_);
                        crate::leanh::lean_dec_ref_known(v___x_2690_, 1);
                        v___x_2692_ = (crate::leanh::lean_unbox(v_a_2691_) as u8);
                        crate::leanh::lean_dec(v_a_2691_);
                        if v___x_2692_ == 0 {
                            v___y_2489_ = v_a_2689_;
                            v___y_2490_ = v___y_2635_;
                            v___y_2491_ = v___y_2637_;
                            v___y_2492_ = v___y_2640_;
                            v___y_2493_ = v___y_2639_;
                            v___y_2494_ = v___y_2641_;
                            v___y_2495_ = v___y_2642_;
                            v___y_2496_ = v___y_2643_;
                            v___y_2497_ = v___y_2644_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___y_2644_);
                            crate::leanh::lean_inc_ref(v___y_2643_);
                            crate::leanh::lean_inc(v___y_2642_);
                            crate::leanh::lean_inc_ref(v___y_2641_);
                            crate::leanh::lean_inc(v_a_2689_);
                            v___x_2693_ = lean_infer_type(
                                v_a_2689_,
                                v___y_2641_,
                                v___y_2642_,
                                v___y_2643_,
                                v___y_2644_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2693_) == 0 {
                                v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                                crate::leanh::lean_inc(v_a_2694_);
                                crate::leanh::lean_dec_ref_known(v___x_2693_, 1);
                                v___x_2695_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__16
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__16_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__16,
                                );
                                crate::leanh::lean_inc(v_a_2689_);
                                v___x_2696_ = l_Lean_indentExpr(v_a_2689_);
                                v___x_2697_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2697_, 0, v___x_2695_);
                                crate::leanh::lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                                v___x_2698_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__18
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__18_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__18,
                                );
                                v___x_2699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2699_, 0, v___x_2697_);
                                crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                                v___x_2700_ = l_Lean_indentExpr(v_a_2694_);
                                v___x_2701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2701_, 0, v___x_2699_);
                                crate::leanh::lean_ctor_set(v___x_2701_, 1, v___x_2700_);
                                crate::leanh::lean_inc(v___y_2637_);
                                v___x_2702_ =
                                    l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                                        v___y_2637_,
                                        v___x_2701_,
                                        v___y_2641_,
                                        v___y_2642_,
                                        v___y_2643_,
                                        v___y_2644_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_2702_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2702_, 1);
                                    v___y_2489_ = v_a_2689_;
                                    v___y_2490_ = v___y_2635_;
                                    v___y_2491_ = v___y_2637_;
                                    v___y_2492_ = v___y_2640_;
                                    v___y_2493_ = v___y_2639_;
                                    v___y_2494_ = v___y_2641_;
                                    v___y_2495_ = v___y_2642_;
                                    v___y_2496_ = v___y_2643_;
                                    v___y_2497_ = v___y_2644_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_2689_);
                                    crate::leanh::lean_dec(v___y_2644_);
                                    crate::leanh::lean_dec_ref(v___y_2643_);
                                    crate::leanh::lean_dec(v___y_2642_);
                                    crate::leanh::lean_dec_ref(v___y_2641_);
                                    crate::leanh::lean_dec_ref(v___y_2640_);
                                    crate::leanh::lean_dec_ref(v___y_2639_);
                                    crate::leanh::lean_dec(v___y_2637_);
                                    crate::leanh::lean_dec_ref(v___y_2635_);
                                    crate::leanh::lean_dec(v_fvarId_2462_);
                                    crate::leanh::lean_dec(v___x_2461_);
                                    crate::leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2703_ = crate::leanh::lean_ctor_get(v___x_2702_, 0);
                                    v_isSharedCheck_2710_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2702_)) as u8;
                                    if v_isSharedCheck_2710_ == 0 {
                                        v___x_2705_ = v___x_2702_;
                                        v_isShared_2706_ = v_isSharedCheck_2710_;
                                        state = 30;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2703_);
                                        crate::leanh::lean_dec(v___x_2702_);
                                        v___x_2705_ = crate::leanh::lean_box(0);
                                        v_isShared_2706_ = v_isSharedCheck_2710_;
                                        state = 30;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2689_);
                                crate::leanh::lean_dec(v___y_2644_);
                                crate::leanh::lean_dec_ref(v___y_2643_);
                                crate::leanh::lean_dec(v___y_2642_);
                                crate::leanh::lean_dec_ref(v___y_2641_);
                                crate::leanh::lean_dec_ref(v___y_2640_);
                                crate::leanh::lean_dec_ref(v___y_2639_);
                                crate::leanh::lean_dec(v___y_2637_);
                                crate::leanh::lean_dec_ref(v___y_2635_);
                                crate::leanh::lean_dec(v_fvarId_2462_);
                                crate::leanh::lean_dec(v___x_2461_);
                                crate::leanh::lean_dec(v_mvarId_2460_);
                                v_a_2711_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                                v_isSharedCheck_2718_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2693_)) as u8;
                                if v_isSharedCheck_2718_ == 0 {
                                    v___x_2713_ = v___x_2693_;
                                    v_isShared_2714_ = v_isSharedCheck_2718_;
                                    state = 32;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2711_);
                                    crate::leanh::lean_dec(v___x_2693_);
                                    v___x_2713_ = crate::leanh::lean_box(0);
                                    v_isShared_2714_ = v_isSharedCheck_2718_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2689_);
                        crate::leanh::lean_dec(v___y_2644_);
                        crate::leanh::lean_dec_ref(v___y_2643_);
                        crate::leanh::lean_dec(v___y_2642_);
                        crate::leanh::lean_dec_ref(v___y_2641_);
                        crate::leanh::lean_dec_ref(v___y_2640_);
                        crate::leanh::lean_dec_ref(v___y_2639_);
                        crate::leanh::lean_dec(v___y_2637_);
                        crate::leanh::lean_dec_ref(v___y_2635_);
                        crate::leanh::lean_dec(v_fvarId_2462_);
                        crate::leanh::lean_dec(v___x_2461_);
                        crate::leanh::lean_dec(v_mvarId_2460_);
                        v_a_2719_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2726_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2726_ == 0 {
                            v___x_2721_ = v___x_2690_;
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2719_);
                            crate::leanh::lean_dec(v___x_2690_);
                            v___x_2721_ = crate::leanh::lean_box(0);
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2644_);
                    crate::leanh::lean_dec_ref(v___y_2643_);
                    crate::leanh::lean_dec(v___y_2642_);
                    crate::leanh::lean_dec_ref(v___y_2641_);
                    crate::leanh::lean_dec_ref(v___y_2640_);
                    crate::leanh::lean_dec_ref(v___y_2639_);
                    crate::leanh::lean_dec(v___y_2637_);
                    crate::leanh::lean_dec_ref(v___y_2635_);
                    crate::leanh::lean_dec(v_fvarId_2462_);
                    crate::leanh::lean_dec(v___x_2461_);
                    crate::leanh::lean_dec(v_mvarId_2460_);
                    v_a_2727_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2734_ = (!crate::leanh::lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2734_ == 0 {
                        v___x_2729_ = v___x_2688_;
                        v_isShared_2730_ = v_isSharedCheck_2734_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2727_);
                        crate::leanh::lean_dec(v___x_2688_);
                        v___x_2729_ = crate::leanh::lean_box(0);
                        v_isShared_2730_ = v_isSharedCheck_2734_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                if v_isShared_2706_ == 0 {
                    v___x_2708_ = v___x_2705_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
                    v___x_2708_ = v_reuseFailAlloc_2709_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2708_;
            }
            32 => {
                if v_isShared_2714_ == 0 {
                    v___x_2716_ = v___x_2713_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2717_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
                    v___x_2716_ = v_reuseFailAlloc_2717_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2716_;
            }
            34 => {
                if v_isShared_2722_ == 0 {
                    v___x_2724_ = v___x_2721_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2724_;
            }
            36 => {
                if v_isShared_2730_ == 0 {
                    v___x_2732_ = v___x_2729_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
                    v___x_2732_ = v_reuseFailAlloc_2733_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2732_;
            }
            38 => {
                v___x_2744_ = l_Lean_Meta_injectionCore___lam__1___closed__20;
                v___x_2745_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2746_ = l_Lean_Expr_isAppOfArity(v_type_2738_, v___x_2744_, v___x_2745_);
                if v___x_2746_ == 0 {
                    crate::leanh::lean_dec_ref(v_prf_2739_);
                    crate::leanh::lean_dec_ref(v_type_2738_);
                    crate::leanh::lean_dec_ref(v___x_2463_);
                    crate::leanh::lean_dec(v_fvarId_2462_);
                    v___x_2747_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__24),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_injectionCore___lam__1___closed__24_once
                        ),
                        _init_l_Lean_Meta_injectionCore___lam__1___closed__24,
                    );
                    v___x_2748_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_2461_,
                        v_mvarId_2460_,
                        v___x_2747_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    crate::leanh::lean_dec(v___y_2743_);
                    crate::leanh::lean_dec_ref(v___y_2742_);
                    crate::leanh::lean_dec(v___y_2741_);
                    crate::leanh::lean_dec_ref(v___y_2740_);
                    return v___x_2748_;
                } else {
                    crate::leanh::lean_inc(v_mvarId_2460_);
                    v___x_2749_ = l_Lean_MVarId_getType(
                        v_mvarId_2460_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2749_) == 0 {
                        v_a_2750_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                        crate::leanh::lean_inc(v_a_2750_);
                        crate::leanh::lean_dec_ref_known(v___x_2749_, 1);
                        v___x_2751_ = l_Lean_Expr_appFn_x21(v_type_2738_);
                        v___x_2752_ = l_Lean_Expr_appArg_x21(v___x_2751_);
                        crate::leanh::lean_dec_ref(v___x_2751_);
                        v___x_2753_ = l_Lean_Meta_isConstructorApp_x27_x3f(
                            v___x_2752_,
                            v___y_2740_,
                            v___y_2741_,
                            v___y_2742_,
                            v___y_2743_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2753_) == 0 {
                            v_a_2754_ = crate::leanh::lean_ctor_get(v___x_2753_, 0);
                            crate::leanh::lean_inc(v_a_2754_);
                            crate::leanh::lean_dec_ref_known(v___x_2753_, 1);
                            v___x_2755_ = l_Lean_Expr_appArg_x21(v_type_2738_);
                            crate::leanh::lean_dec_ref(v_type_2738_);
                            v___x_2756_ = l_Lean_Meta_isConstructorApp_x27_x3f(
                                v___x_2755_,
                                v___y_2740_,
                                v___y_2741_,
                                v___y_2742_,
                                v___y_2743_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2756_) == 0 {
                                if crate::leanh::lean_obj_tag(v_a_2754_) == 1 {
                                    v_a_2757_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                                    crate::leanh::lean_inc(v_a_2757_);
                                    crate::leanh::lean_dec_ref_known(v___x_2756_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2757_) == 1 {
                                        v_val_2758_ = crate::leanh::lean_ctor_get(v_a_2754_, 0);
                                        crate::leanh::lean_inc(v_val_2758_);
                                        crate::leanh::lean_dec_ref_known(v_a_2754_, 1);
                                        v_val_2759_ = crate::leanh::lean_ctor_get(v_a_2757_, 0);
                                        crate::leanh::lean_inc(v_val_2759_);
                                        crate::leanh::lean_dec_ref_known(v_a_2757_, 1);
                                        v___x_2760_ =
                                            l_Lean_Meta_injectionCore___lam__1___closed__25;
                                        v___x_2761_ =
                                            l_Lean_Meta_injectionCore___lam__1___closed__26;
                                        v___x_2762_ = l_Lean_Name_mkStr3(
                                            v___x_2760_,
                                            v___x_2761_,
                                            v___x_2463_,
                                        );
                                        crate::leanh::lean_inc_n(v___x_2762_, 2);
                                        v___f_2763_ = crate::leanh::lean_alloc_closure(
                                            l_Lean_Meta_injectionCore___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            6,
                                            1,
                                        );
                                        crate::leanh::lean_closure_set(v___f_2763_, 0, v___x_2762_);
                                        v___x_2764_ = l_Lean_Meta_injectionCore___lam__0(
                                            v___x_2762_,
                                            v___y_2740_,
                                            v___y_2741_,
                                            v___y_2742_,
                                            v___y_2743_,
                                        );
                                        v_a_2765_ = crate::leanh::lean_ctor_get(v___x_2764_, 0);
                                        v_isSharedCheck_2798_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2764_)) as u8;
                                        if v_isSharedCheck_2798_ == 0 {
                                            v___x_2767_ = v___x_2764_;
                                            v_isShared_2768_ = v_isSharedCheck_2798_;
                                            state = 39;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2765_);
                                            crate::leanh::lean_dec(v___x_2764_);
                                            v___x_2767_ = crate::leanh::lean_box(0);
                                            v_isShared_2768_ = v_isSharedCheck_2798_;
                                            state = 39;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2757_);
                                        crate::leanh::lean_dec_ref_known(v_a_2754_, 1);
                                        crate::leanh::lean_dec(v_a_2750_);
                                        crate::leanh::lean_dec_ref(v_prf_2739_);
                                        crate::leanh::lean_dec_ref(v___x_2463_);
                                        crate::leanh::lean_dec(v_fvarId_2462_);
                                        v___y_2477_ = v___y_2740_;
                                        v___y_2478_ = v___y_2741_;
                                        v___y_2479_ = v___y_2742_;
                                        v___y_2480_ = v___y_2743_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_2756_, 1);
                                    crate::leanh::lean_dec(v_a_2754_);
                                    crate::leanh::lean_dec(v_a_2750_);
                                    crate::leanh::lean_dec_ref(v_prf_2739_);
                                    crate::leanh::lean_dec_ref(v___x_2463_);
                                    crate::leanh::lean_dec(v_fvarId_2462_);
                                    v___y_2477_ = v___y_2740_;
                                    v___y_2478_ = v___y_2741_;
                                    v___y_2479_ = v___y_2742_;
                                    v___y_2480_ = v___y_2743_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2754_);
                                crate::leanh::lean_dec(v_a_2750_);
                                crate::leanh::lean_dec(v___y_2743_);
                                crate::leanh::lean_dec_ref(v___y_2742_);
                                crate::leanh::lean_dec(v___y_2741_);
                                crate::leanh::lean_dec_ref(v___y_2740_);
                                crate::leanh::lean_dec_ref(v_prf_2739_);
                                crate::leanh::lean_dec_ref(v___x_2463_);
                                crate::leanh::lean_dec(v_fvarId_2462_);
                                crate::leanh::lean_dec(v___x_2461_);
                                crate::leanh::lean_dec(v_mvarId_2460_);
                                v_a_2799_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                                v_isSharedCheck_2806_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2756_)) as u8;
                                if v_isSharedCheck_2806_ == 0 {
                                    v___x_2801_ = v___x_2756_;
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 45;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2799_);
                                    crate::leanh::lean_dec(v___x_2756_);
                                    v___x_2801_ = crate::leanh::lean_box(0);
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 45;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2750_);
                            crate::leanh::lean_dec(v___y_2743_);
                            crate::leanh::lean_dec_ref(v___y_2742_);
                            crate::leanh::lean_dec(v___y_2741_);
                            crate::leanh::lean_dec_ref(v___y_2740_);
                            crate::leanh::lean_dec_ref(v_prf_2739_);
                            crate::leanh::lean_dec_ref(v_type_2738_);
                            crate::leanh::lean_dec_ref(v___x_2463_);
                            crate::leanh::lean_dec(v_fvarId_2462_);
                            crate::leanh::lean_dec(v___x_2461_);
                            crate::leanh::lean_dec(v_mvarId_2460_);
                            v_a_2807_ = crate::leanh::lean_ctor_get(v___x_2753_, 0);
                            v_isSharedCheck_2814_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2753_)) as u8;
                            if v_isSharedCheck_2814_ == 0 {
                                v___x_2809_ = v___x_2753_;
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2807_);
                                crate::leanh::lean_dec(v___x_2753_);
                                v___x_2809_ = crate::leanh::lean_box(0);
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_2743_);
                        crate::leanh::lean_dec_ref(v___y_2742_);
                        crate::leanh::lean_dec(v___y_2741_);
                        crate::leanh::lean_dec_ref(v___y_2740_);
                        crate::leanh::lean_dec_ref(v_prf_2739_);
                        crate::leanh::lean_dec_ref(v_type_2738_);
                        crate::leanh::lean_dec_ref(v___x_2463_);
                        crate::leanh::lean_dec(v_fvarId_2462_);
                        crate::leanh::lean_dec(v___x_2461_);
                        crate::leanh::lean_dec(v_mvarId_2460_);
                        v_a_2815_ = crate::leanh::lean_ctor_get(v___x_2749_, 0);
                        v_isSharedCheck_2822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2749_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2749_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2815_);
                            crate::leanh::lean_dec(v___x_2749_);
                            v___x_2817_ = crate::leanh::lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            39 => {
                v___x_2769_ = (crate::leanh::lean_unbox(v_a_2765_) as u8);
                crate::leanh::lean_dec(v_a_2765_);
                if v___x_2769_ == 0 {
                    crate::leanh::lean_del_object(v___x_2767_);
                    v___y_2635_ = v___f_2763_;
                    v___y_2636_ = v_a_2750_;
                    v___y_2637_ = v___x_2762_;
                    v___y_2638_ = v_prf_2739_;
                    v___y_2639_ = v_val_2758_;
                    v___y_2640_ = v_val_2759_;
                    v___y_2641_ = v___y_2740_;
                    v___y_2642_ = v___y_2741_;
                    v___y_2643_ = v___y_2742_;
                    v___y_2644_ = v___y_2743_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_2743_);
                    crate::leanh::lean_inc_ref(v___y_2742_);
                    crate::leanh::lean_inc(v___y_2741_);
                    crate::leanh::lean_inc_ref(v___y_2740_);
                    crate::leanh::lean_inc_ref(v_prf_2739_);
                    v___x_2770_ = lean_infer_type(
                        v_prf_2739_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2770_) == 0 {
                        v_a_2771_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                        crate::leanh::lean_inc(v_a_2771_);
                        crate::leanh::lean_dec_ref_known(v___x_2770_, 1);
                        v___x_2772_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__28
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__28_once
                            ),
                            _init_l_Lean_Meta_injectionCore___lam__1___closed__28,
                        );
                        v___x_2773_ = l_Lean_MessageData_ofExpr(v_a_2771_);
                        v___x_2774_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2774_, 0, v___x_2772_);
                        crate::leanh::lean_ctor_set(v___x_2774_, 1, v___x_2773_);
                        v___x_2775_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__30_once
                            ),
                            _init_l_Lean_Meta_injectionCore___lam__1___closed__30,
                        );
                        v___x_2776_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2776_, 0, v___x_2774_);
                        crate::leanh::lean_ctor_set(v___x_2776_, 1, v___x_2775_);
                        crate::leanh::lean_inc(v_mvarId_2460_);
                        if v_isShared_2768_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2767_, 1);
                            crate::leanh::lean_ctor_set(v___x_2767_, 0, v_mvarId_2460_);
                            v___x_2778_ = v___x_2767_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_2789_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_mvarId_2460_);
                            v___x_2778_ = v_reuseFailAlloc_2789_;
                            state = 40;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2767_);
                        crate::leanh::lean_dec_ref(v___f_2763_);
                        crate::leanh::lean_dec(v___x_2762_);
                        crate::leanh::lean_dec(v_val_2759_);
                        crate::leanh::lean_dec(v_val_2758_);
                        crate::leanh::lean_dec(v_a_2750_);
                        crate::leanh::lean_dec(v___y_2743_);
                        crate::leanh::lean_dec_ref(v___y_2742_);
                        crate::leanh::lean_dec(v___y_2741_);
                        crate::leanh::lean_dec_ref(v___y_2740_);
                        crate::leanh::lean_dec_ref(v_prf_2739_);
                        crate::leanh::lean_dec(v_fvarId_2462_);
                        crate::leanh::lean_dec(v___x_2461_);
                        crate::leanh::lean_dec(v_mvarId_2460_);
                        v_a_2790_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                        v_isSharedCheck_2797_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2770_)) as u8;
                        if v_isSharedCheck_2797_ == 0 {
                            v___x_2792_ = v___x_2770_;
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2790_);
                            crate::leanh::lean_dec(v___x_2770_);
                            v___x_2792_ = crate::leanh::lean_box(0);
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 43;
                            continue;
                        }
                    }
                }
            }
            40 => {
                v___x_2779_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2779_, 0, v___x_2776_);
                crate::leanh::lean_ctor_set(v___x_2779_, 1, v___x_2778_);
                crate::leanh::lean_inc(v___x_2762_);
                v___x_2780_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                    v___x_2762_,
                    v___x_2779_,
                    v___y_2740_,
                    v___y_2741_,
                    v___y_2742_,
                    v___y_2743_,
                );
                if crate::leanh::lean_obj_tag(v___x_2780_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2780_, 1);
                    v___y_2635_ = v___f_2763_;
                    v___y_2636_ = v_a_2750_;
                    v___y_2637_ = v___x_2762_;
                    v___y_2638_ = v_prf_2739_;
                    v___y_2639_ = v_val_2758_;
                    v___y_2640_ = v_val_2759_;
                    v___y_2641_ = v___y_2740_;
                    v___y_2642_ = v___y_2741_;
                    v___y_2643_ = v___y_2742_;
                    v___y_2644_ = v___y_2743_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___f_2763_);
                    crate::leanh::lean_dec(v___x_2762_);
                    crate::leanh::lean_dec(v_val_2759_);
                    crate::leanh::lean_dec(v_val_2758_);
                    crate::leanh::lean_dec(v_a_2750_);
                    crate::leanh::lean_dec(v___y_2743_);
                    crate::leanh::lean_dec_ref(v___y_2742_);
                    crate::leanh::lean_dec(v___y_2741_);
                    crate::leanh::lean_dec_ref(v___y_2740_);
                    crate::leanh::lean_dec_ref(v_prf_2739_);
                    crate::leanh::lean_dec(v_fvarId_2462_);
                    crate::leanh::lean_dec(v___x_2461_);
                    crate::leanh::lean_dec(v_mvarId_2460_);
                    v_a_2781_ = crate::leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2788_ = (!crate::leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2783_ = v___x_2780_;
                        v_isShared_2784_ = v_isSharedCheck_2788_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2781_);
                        crate::leanh::lean_dec(v___x_2780_);
                        v___x_2783_ = crate::leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2788_;
                        state = 41;
                        continue;
                    }
                }
            }
            41 => {
                if v_isShared_2784_ == 0 {
                    v___x_2786_ = v___x_2783_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
                    v___x_2786_ = v_reuseFailAlloc_2787_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2786_;
            }
            43 => {
                if v_isShared_2793_ == 0 {
                    v___x_2795_ = v___x_2792_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2795_;
            }
            45 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2804_;
            }
            47 => {
                if v_isShared_2810_ == 0 {
                    v___x_2812_ = v___x_2809_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
                    v___x_2812_ = v_reuseFailAlloc_2813_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2812_;
            }
            49 => {
                if v_isShared_2818_ == 0 {
                    v___x_2820_ = v___x_2817_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
                    v___x_2820_ = v_reuseFailAlloc_2821_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2820_;
            }
            51 => {
                if v_isShared_2850_ == 0 {
                    v___x_2852_ = v___x_2849_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_2853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
                    v___x_2852_ = v_reuseFailAlloc_2853_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_2852_;
            }
            53 => {
                if v_isShared_2858_ == 0 {
                    v___x_2860_ = v___x_2857_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
                    v___x_2860_ = v_reuseFailAlloc_2861_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_2860_;
            }
            55 => {
                if v_isShared_2866_ == 0 {
                    v___x_2868_ = v___x_2865_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2868_;
            }
            57 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_2876_;
            }
            59 => {
                if v_isShared_2882_ == 0 {
                    v___x_2884_ = v___x_2881_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2884_;
            }
            61 => {
                if v_isShared_2890_ == 0 {
                    v___x_2892_ = v___x_2889_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
                    v___x_2892_ = v_reuseFailAlloc_2893_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__1___boxed(
    mut v_mvarId_2895_: *mut crate::leanh::LeanObject,
    mut v___x_2896_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2897_: *mut crate::leanh::LeanObject,
    mut v___x_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2904_ = l_Lean_Meta_injectionCore___lam__1(
        v_mvarId_2895_,
        v___x_2896_,
        v_fvarId_2897_,
        v___x_2898_,
        v___y_2899_,
        v___y_2900_,
        v___y_2901_,
        v___y_2902_,
    );
    return v_res_2904_;
}
pub unsafe fn l_Lean_Meta_injectionCore(
    mut v_mvarId_2908_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Meta_injectionCore___closed__0;
    v___x_2916_ = l_Lean_Meta_injectionCore___closed__1;
    crate::leanh::lean_inc(v_mvarId_2908_);
    v___f_2917_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_injectionCore___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2917_, 0, v_mvarId_2908_);
    crate::leanh::lean_closure_set(v___f_2917_, 1, v___x_2916_);
    crate::leanh::lean_closure_set(v___f_2917_, 2, v_fvarId_2909_);
    crate::leanh::lean_closure_set(v___f_2917_, 3, v___x_2915_);
    v___x_2918_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
        v_mvarId_2908_,
        v___f_2917_,
        v_a_2910_,
        v_a_2911_,
        v_a_2912_,
        v_a_2913_,
    );
    return v___x_2918_;
}
pub unsafe fn l_Lean_Meta_injectionCore___boxed(
    mut v_mvarId_2919_: *mut crate::leanh::LeanObject,
    mut v_fvarId_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
    mut v_a_2924_: *mut crate::leanh::LeanObject,
    mut v_a_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Lean_Meta_injectionCore(
        v_mvarId_2919_,
        v_fvarId_2920_,
        v_a_2921_,
        v_a_2922_,
        v_a_2923_,
        v_a_2924_,
    );
    crate::leanh::lean_dec(v_a_2924_);
    crate::leanh::lean_dec_ref(v_a_2923_);
    crate::leanh::lean_dec(v_a_2922_);
    crate::leanh::lean_dec_ref(v_a_2921_);
    return v_res_2926_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(
    mut v_mvarId_2927_: *mut crate::leanh::LeanObject,
    mut v_val_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
        v_mvarId_2927_,
        v_val_2928_,
        v___y_2930_,
    );
    return v___x_2934_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(
    mut v_mvarId_2935_: *mut crate::leanh::LeanObject,
    mut v_val_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(
        v_mvarId_2935_,
        v_val_2936_,
        v___y_2937_,
        v___y_2938_,
        v___y_2939_,
        v___y_2940_,
    );
    crate::leanh::lean_dec(v___y_2940_);
    crate::leanh::lean_dec_ref(v___y_2939_);
    crate::leanh::lean_dec(v___y_2938_);
    crate::leanh::lean_dec_ref(v___y_2937_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(
    mut v_00_u03b2_2943_: *mut crate::leanh::LeanObject,
    mut v_x_2944_: *mut crate::leanh::LeanObject,
    mut v_x_2945_: *mut crate::leanh::LeanObject,
    mut v_x_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_2944_, v_x_2945_, v_x_2946_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2948_: *mut crate::leanh::LeanObject,
    mut v_x_2949_: *mut crate::leanh::LeanObject,
    mut v_x_2950_: usize,
    mut v_x_2951_: usize,
    mut v_x_2952_: *mut crate::leanh::LeanObject,
    mut v_x_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2949_, v_x_2950_, v_x_2951_, v_x_2952_, v_x_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2955_: *mut crate::leanh::LeanObject,
    mut v_x_2956_: *mut crate::leanh::LeanObject,
    mut v_x_2957_: *mut crate::leanh::LeanObject,
    mut v_x_2958_: *mut crate::leanh::LeanObject,
    mut v_x_2959_: *mut crate::leanh::LeanObject,
    mut v_x_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17908__boxed_2961_: usize = 0;
    let mut v_x_17909__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17908__boxed_2961_ = crate::leanh::lean_unbox_usize(v_x_2957_);
    crate::leanh::lean_dec(v_x_2957_);
    v_x_17909__boxed_2962_ = crate::leanh::lean_unbox_usize(v_x_2958_);
    crate::leanh::lean_dec(v_x_2958_);
    v_res_2963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_2955_, v_x_2956_, v_x_17908__boxed_2961_, v_x_17909__boxed_2962_, v_x_2959_, v_x_2960_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_2964_: *mut crate::leanh::LeanObject,
    mut v_n_2965_: *mut crate::leanh::LeanObject,
    mut v_k_2966_: *mut crate::leanh::LeanObject,
    mut v_v_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_2965_, v_k_2966_, v_v_2967_);
    return v___x_2968_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_2969_: *mut crate::leanh::LeanObject,
    mut v_depth_2970_: usize,
    mut v_keys_2971_: *mut crate::leanh::LeanObject,
    mut v_vals_2972_: *mut crate::leanh::LeanObject,
    mut v_heq_2973_: *mut crate::leanh::LeanObject,
    mut v_i_2974_: *mut crate::leanh::LeanObject,
    mut v_entries_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_2970_, v_keys_2971_, v_vals_2972_, v_i_2974_, v_entries_2975_);
    return v___x_2976_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_2977_: *mut crate::leanh::LeanObject,
    mut v_depth_2978_: *mut crate::leanh::LeanObject,
    mut v_keys_2979_: *mut crate::leanh::LeanObject,
    mut v_vals_2980_: *mut crate::leanh::LeanObject,
    mut v_heq_2981_: *mut crate::leanh::LeanObject,
    mut v_i_2982_: *mut crate::leanh::LeanObject,
    mut v_entries_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2984_: usize = 0;
    let mut v_res_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2984_ = crate::leanh::lean_unbox_usize(v_depth_2978_);
    crate::leanh::lean_dec(v_depth_2978_);
    v_res_2985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_2977_, v_depth_boxed_2984_, v_keys_2979_, v_vals_2980_, v_heq_2981_, v_i_2982_, v_entries_2983_);
    crate::leanh::lean_dec_ref(v_vals_2980_);
    crate::leanh::lean_dec_ref(v_keys_2979_);
    return v_res_2985_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_2986_: *mut crate::leanh::LeanObject,
    mut v_x_2987_: *mut crate::leanh::LeanObject,
    mut v_x_2988_: *mut crate::leanh::LeanObject,
    mut v_x_2989_: *mut crate::leanh::LeanObject,
    mut v_x_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_2987_, v_x_2988_, v_x_2989_, v_x_2990_);
    return v___x_2991_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorIdx(
    mut v_x_2992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2992_) == 0 {
        let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2993_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2993_;
    } else {
        let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2994_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2994_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorIdx___boxed(
    mut v_x_2995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2996_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_2995_);
    crate::leanh::lean_dec(v_x_2995_);
    return v_res_2996_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim___redArg(
    mut v_t_2997_: *mut crate::leanh::LeanObject,
    mut v_k_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2997_) == 0 {
        return v_k_2998_;
    } else {
        let mut v_mvarId_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_newEqs_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_remainingNames_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_2999_ = crate::leanh::lean_ctor_get(v_t_2997_, 0);
        crate::leanh::lean_inc(v_mvarId_2999_);
        v_newEqs_3000_ = crate::leanh::lean_ctor_get(v_t_2997_, 1);
        crate::leanh::lean_inc_ref(v_newEqs_3000_);
        v_remainingNames_3001_ = crate::leanh::lean_ctor_get(v_t_2997_, 2);
        crate::leanh::lean_inc(v_remainingNames_3001_);
        crate::leanh::lean_dec_ref_known(v_t_2997_, 3);
        v___x_3002_ = crate::leanh::lean_apply_3(
            v_k_2998_,
            v_mvarId_2999_,
            v_newEqs_3000_,
            v_remainingNames_3001_,
        );
        return v___x_3002_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim(
    mut v_motive_3003_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3004_: *mut crate::leanh::LeanObject,
    mut v_t_3005_: *mut crate::leanh::LeanObject,
    mut v_h_3006_: *mut crate::leanh::LeanObject,
    mut v_k_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3005_, v_k_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim___boxed(
    mut v_motive_3009_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3010_: *mut crate::leanh::LeanObject,
    mut v_t_3011_: *mut crate::leanh::LeanObject,
    mut v_h_3012_: *mut crate::leanh::LeanObject,
    mut v_k_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3014_ = l_Lean_Meta_InjectionResult_ctorElim(
        v_motive_3009_,
        v_ctorIdx_3010_,
        v_t_3011_,
        v_h_3012_,
        v_k_3013_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3010_);
    return v_res_3014_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_solved_elim___redArg(
    mut v_t_3015_: *mut crate::leanh::LeanObject,
    mut v_solved_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3015_, v_solved_3016_);
    return v___x_3017_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_solved_elim(
    mut v_motive_3018_: *mut crate::leanh::LeanObject,
    mut v_t_3019_: *mut crate::leanh::LeanObject,
    mut v_h_3020_: *mut crate::leanh::LeanObject,
    mut v_solved_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3022_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3019_, v_solved_3021_);
    return v___x_3022_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_subgoal_elim___redArg(
    mut v_t_3023_: *mut crate::leanh::LeanObject,
    mut v_subgoal_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3023_, v_subgoal_3024_);
    return v___x_3025_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_subgoal_elim(
    mut v_motive_3026_: *mut crate::leanh::LeanObject,
    mut v_t_3027_: *mut crate::leanh::LeanObject,
    mut v_h_3028_: *mut crate::leanh::LeanObject,
    mut v_subgoal_3029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3027_, v_subgoal_3029_);
    return v___x_3030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(
    mut v_tryToClear_3031_: u8,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3042_: u8 = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3064_: u8 = 0;
    let mut v_a_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_head_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_a_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3041_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3042_ = lean_nat_dec_eq(v_a_3032_, v_zero_3041_);
                if v_isZero_3042_ == 1 {
                    crate::leanh::lean_dec(v_a_3032_);
                    v___x_3043_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3043_, 0, v_a_3033_);
                    crate::leanh::lean_ctor_set(v___x_3043_, 1, v_a_3034_);
                    crate::leanh::lean_ctor_set(v___x_3043_, 2, v_a_3035_);
                    v___x_3044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
                    return v___x_3044_;
                } else {
                    v_one_3045_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3046_ = lean_nat_sub(v_a_3032_, v_one_3045_);
                    crate::leanh::lean_dec(v_a_3032_);
                    if crate::leanh::lean_obj_tag(v_a_3035_) == 0 {
                        v___x_3047_ = l_Lean_Meta_intro1Core(
                            v_a_3033_,
                            v_isZero_3042_,
                            v_a_3036_,
                            v_a_3037_,
                            v_a_3038_,
                            v_a_3039_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3047_) == 0 {
                            v_a_3048_ = crate::leanh::lean_ctor_get(v___x_3047_, 0);
                            crate::leanh::lean_inc(v_a_3048_);
                            crate::leanh::lean_dec_ref_known(v___x_3047_, 1);
                            v_fst_3049_ = crate::leanh::lean_ctor_get(v_a_3048_, 0);
                            crate::leanh::lean_inc(v_fst_3049_);
                            v_snd_3050_ = crate::leanh::lean_ctor_get(v_a_3048_, 1);
                            crate::leanh::lean_inc(v_snd_3050_);
                            crate::leanh::lean_dec(v_a_3048_);
                            v___x_3051_ = l_Lean_Meta_heqToEq(
                                v_snd_3050_,
                                v_fst_3049_,
                                v_tryToClear_3031_,
                                v_a_3036_,
                                v_a_3037_,
                                v_a_3038_,
                                v_a_3039_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                                v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                                crate::leanh::lean_inc(v_a_3052_);
                                crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                                v_fst_3053_ = crate::leanh::lean_ctor_get(v_a_3052_, 0);
                                crate::leanh::lean_inc(v_fst_3053_);
                                v_snd_3054_ = crate::leanh::lean_ctor_get(v_a_3052_, 1);
                                crate::leanh::lean_inc(v_snd_3054_);
                                crate::leanh::lean_dec(v_a_3052_);
                                v___x_3055_ = lean_array_push(v_a_3034_, v_fst_3053_);
                                v_a_3032_ = v_n_3046_;
                                v_a_3033_ = v_snd_3054_;
                                v_a_3034_ = v___x_3055_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_n_3046_);
                                crate::leanh::lean_dec_ref(v_a_3034_);
                                v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                                v_isSharedCheck_3064_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3051_)) as u8;
                                if v_isSharedCheck_3064_ == 0 {
                                    v___x_3059_ = v___x_3051_;
                                    v_isShared_3060_ = v_isSharedCheck_3064_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3057_);
                                    crate::leanh::lean_dec(v___x_3051_);
                                    v___x_3059_ = crate::leanh::lean_box(0);
                                    v_isShared_3060_ = v_isSharedCheck_3064_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_n_3046_);
                            crate::leanh::lean_dec_ref(v_a_3034_);
                            v_a_3065_ = crate::leanh::lean_ctor_get(v___x_3047_, 0);
                            v_isSharedCheck_3072_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3047_)) as u8;
                            if v_isSharedCheck_3072_ == 0 {
                                v___x_3067_ = v___x_3047_;
                                v_isShared_3068_ = v_isSharedCheck_3072_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3065_);
                                crate::leanh::lean_dec(v___x_3047_);
                                v___x_3067_ = crate::leanh::lean_box(0);
                                v_isShared_3068_ = v_isSharedCheck_3072_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_head_3073_ = crate::leanh::lean_ctor_get(v_a_3035_, 0);
                        crate::leanh::lean_inc(v_head_3073_);
                        v_tail_3074_ = crate::leanh::lean_ctor_get(v_a_3035_, 1);
                        crate::leanh::lean_inc(v_tail_3074_);
                        crate::leanh::lean_dec_ref_known(v_a_3035_, 2);
                        v___x_3075_ = l_Lean_MVarId_intro(
                            v_a_3033_,
                            v_head_3073_,
                            v_a_3036_,
                            v_a_3037_,
                            v_a_3038_,
                            v_a_3039_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                            v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                            crate::leanh::lean_inc(v_a_3076_);
                            crate::leanh::lean_dec_ref_known(v___x_3075_, 1);
                            v_fst_3077_ = crate::leanh::lean_ctor_get(v_a_3076_, 0);
                            crate::leanh::lean_inc(v_fst_3077_);
                            v_snd_3078_ = crate::leanh::lean_ctor_get(v_a_3076_, 1);
                            crate::leanh::lean_inc(v_snd_3078_);
                            crate::leanh::lean_dec(v_a_3076_);
                            v___x_3079_ = l_Lean_Meta_heqToEq(
                                v_snd_3078_,
                                v_fst_3077_,
                                v_tryToClear_3031_,
                                v_a_3036_,
                                v_a_3037_,
                                v_a_3038_,
                                v_a_3039_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3079_) == 0 {
                                v_a_3080_ = crate::leanh::lean_ctor_get(v___x_3079_, 0);
                                crate::leanh::lean_inc(v_a_3080_);
                                crate::leanh::lean_dec_ref_known(v___x_3079_, 1);
                                v_fst_3081_ = crate::leanh::lean_ctor_get(v_a_3080_, 0);
                                crate::leanh::lean_inc(v_fst_3081_);
                                v_snd_3082_ = crate::leanh::lean_ctor_get(v_a_3080_, 1);
                                crate::leanh::lean_inc(v_snd_3082_);
                                crate::leanh::lean_dec(v_a_3080_);
                                v___x_3083_ = lean_array_push(v_a_3034_, v_fst_3081_);
                                v_a_3032_ = v_n_3046_;
                                v_a_3033_ = v_snd_3082_;
                                v_a_3034_ = v___x_3083_;
                                v_a_3035_ = v_tail_3074_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_3074_);
                                crate::leanh::lean_dec(v_n_3046_);
                                crate::leanh::lean_dec_ref(v_a_3034_);
                                v_a_3085_ = crate::leanh::lean_ctor_get(v___x_3079_, 0);
                                v_isSharedCheck_3092_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3079_)) as u8;
                                if v_isSharedCheck_3092_ == 0 {
                                    v___x_3087_ = v___x_3079_;
                                    v_isShared_3088_ = v_isSharedCheck_3092_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3085_);
                                    crate::leanh::lean_dec(v___x_3079_);
                                    v___x_3087_ = crate::leanh::lean_box(0);
                                    v_isShared_3088_ = v_isSharedCheck_3092_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_3074_);
                            crate::leanh::lean_dec(v_n_3046_);
                            crate::leanh::lean_dec_ref(v_a_3034_);
                            v_a_3093_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                            v_isSharedCheck_3100_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                            if v_isSharedCheck_3100_ == 0 {
                                v___x_3095_ = v___x_3075_;
                                v_isShared_3096_ = v_isSharedCheck_3100_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3093_);
                                crate::leanh::lean_dec(v___x_3075_);
                                v___x_3095_ = crate::leanh::lean_box(0);
                                v_isShared_3096_ = v_isSharedCheck_3100_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3060_ == 0 {
                    v___x_3062_ = v___x_3059_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
                    v___x_3062_ = v_reuseFailAlloc_3063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3062_;
            }
            3 => {
                if v_isShared_3068_ == 0 {
                    v___x_3070_ = v___x_3067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
                    v___x_3070_ = v_reuseFailAlloc_3071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3070_;
            }
            5 => {
                if v_isShared_3088_ == 0 {
                    v___x_3090_ = v___x_3087_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
                    v___x_3090_ = v_reuseFailAlloc_3091_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3090_;
            }
            7 => {
                if v_isShared_3096_ == 0 {
                    v___x_3098_ = v___x_3095_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
                    v___x_3098_ = v_reuseFailAlloc_3099_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3098_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go___boxed(
    mut v_tryToClear_3101_: *mut crate::leanh::LeanObject,
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_a_3104_: *mut crate::leanh::LeanObject,
    mut v_a_3105_: *mut crate::leanh::LeanObject,
    mut v_a_3106_: *mut crate::leanh::LeanObject,
    mut v_a_3107_: *mut crate::leanh::LeanObject,
    mut v_a_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryToClear_boxed_3111_: u8 = 0;
    let mut v_res_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryToClear_boxed_3111_ = (crate::leanh::lean_unbox(v_tryToClear_3101_) as u8);
    v_res_3112_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(
        v_tryToClear_boxed_3111_,
        v_a_3102_,
        v_a_3103_,
        v_a_3104_,
        v_a_3105_,
        v_a_3106_,
        v_a_3107_,
        v_a_3108_,
        v_a_3109_,
    );
    crate::leanh::lean_dec(v_a_3109_);
    crate::leanh::lean_dec_ref(v_a_3108_);
    crate::leanh::lean_dec(v_a_3107_);
    crate::leanh::lean_dec_ref(v_a_3106_);
    return v_res_3112_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v_cls_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_3119_ = l_Lean_Meta_injectionIntro___closed__1;
    v___x_3120_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
    v___x_3121_ = l_Lean_Name_append(v___x_3120_, v_cls_3119_);
    return v___x_3121_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_Meta_injectionIntro___closed__3;
    v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
    return v___x_3124_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ = l_Lean_Meta_injectionIntro___closed__5;
    v___x_3127_ = l_Lean_stringToMessageData(v___x_3126_);
    return v___x_3127_;
}
pub unsafe fn l_Lean_Meta_injectionIntro(
    mut v_mvarId_3128_: *mut crate::leanh::LeanObject,
    mut v_numEqs_3129_: *mut crate::leanh::LeanObject,
    mut v_newNames_3130_: *mut crate::leanh::LeanObject,
    mut v_tryToClear_3131_: u8,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_a_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3145_: u8 = 0;
    let mut v_inheritedTraceOptions_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3144_ = crate::leanh::lean_ctor_get(v_a_3134_, 2);
                v_hasTrace_3145_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3144_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3145_ == 0 {
                    v___y_3138_ = v_a_3132_;
                    v___y_3139_ = v_a_3133_;
                    v___y_3140_ = v_a_3134_;
                    v___y_3141_ = v_a_3135_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3146_ = crate::leanh::lean_ctor_get(v_a_3134_, 13);
                    v_cls_3147_ = l_Lean_Meta_injectionIntro___closed__1;
                    v___x_3148_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__2_once),
                        _init_l_Lean_Meta_injectionIntro___closed__2,
                    );
                    v___x_3149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3146_,
                        v_options_3144_,
                        v___x_3148_,
                    );
                    if v___x_3149_ == 0 {
                        v___y_3138_ = v_a_3132_;
                        v___y_3139_ = v_a_3133_;
                        v___y_3140_ = v_a_3134_;
                        v___y_3141_ = v_a_3135_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3150_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__4_once),
                            _init_l_Lean_Meta_injectionIntro___closed__4,
                        );
                        crate::leanh::lean_inc(v_numEqs_3129_);
                        v___x_3151_ = l_Nat_reprFast(v_numEqs_3129_);
                        v___x_3152_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
                        v___x_3153_ = l_Lean_MessageData_ofFormat(v___x_3152_);
                        v___x_3154_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3154_, 0, v___x_3150_);
                        crate::leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                        v___x_3155_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__6_once),
                            _init_l_Lean_Meta_injectionIntro___closed__6,
                        );
                        v___x_3156_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3156_, 0, v___x_3154_);
                        crate::leanh::lean_ctor_set(v___x_3156_, 1, v___x_3155_);
                        crate::leanh::lean_inc(v_mvarId_3128_);
                        v___x_3157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3157_, 0, v_mvarId_3128_);
                        v___x_3158_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3156_);
                        crate::leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                        v___x_3159_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                            v_cls_3147_,
                            v___x_3158_,
                            v_a_3132_,
                            v_a_3133_,
                            v_a_3134_,
                            v_a_3135_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3159_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3159_, 1);
                            v___y_3138_ = v_a_3132_;
                            v___y_3139_ = v_a_3133_;
                            v___y_3140_ = v_a_3134_;
                            v___y_3141_ = v_a_3135_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_newNames_3130_);
                            crate::leanh::lean_dec(v_numEqs_3129_);
                            crate::leanh::lean_dec(v_mvarId_3128_);
                            v_a_3160_ = crate::leanh::lean_ctor_get(v___x_3159_, 0);
                            v_isSharedCheck_3167_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3159_)) as u8;
                            if v_isSharedCheck_3167_ == 0 {
                                v___x_3162_ = v___x_3159_;
                                v_isShared_3163_ = v_isSharedCheck_3167_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3160_);
                                crate::leanh::lean_dec(v___x_3159_);
                                v___x_3162_ = crate::leanh::lean_box(0);
                                v_isShared_3163_ = v_isSharedCheck_3167_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3142_ = l_Lean_Meta_injectionIntro___closed__0;
                v___x_3143_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(
                    v_tryToClear_3131_,
                    v_numEqs_3129_,
                    v_mvarId_3128_,
                    v___x_3142_,
                    v_newNames_3130_,
                    v___y_3138_,
                    v___y_3139_,
                    v___y_3140_,
                    v___y_3141_,
                );
                return v___x_3143_;
            }
            2 => {
                if v_isShared_3163_ == 0 {
                    v___x_3165_ = v___x_3162_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
                    v___x_3165_ = v_reuseFailAlloc_3166_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_injectionIntro___boxed(
    mut v_mvarId_3168_: *mut crate::leanh::LeanObject,
    mut v_numEqs_3169_: *mut crate::leanh::LeanObject,
    mut v_newNames_3170_: *mut crate::leanh::LeanObject,
    mut v_tryToClear_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryToClear_boxed_3177_: u8 = 0;
    let mut v_res_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryToClear_boxed_3177_ = (crate::leanh::lean_unbox(v_tryToClear_3171_) as u8);
    v_res_3178_ = l_Lean_Meta_injectionIntro(
        v_mvarId_3168_,
        v_numEqs_3169_,
        v_newNames_3170_,
        v_tryToClear_boxed_3177_,
        v_a_3172_,
        v_a_3173_,
        v_a_3174_,
        v_a_3175_,
    );
    crate::leanh::lean_dec(v_a_3175_);
    crate::leanh::lean_dec_ref(v_a_3174_);
    crate::leanh::lean_dec(v_a_3173_);
    crate::leanh::lean_dec_ref(v_a_3172_);
    return v_res_3178_;
}
pub unsafe fn l_Lean_Meta_injection(
    mut v_mvarId_3179_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3180_: *mut crate::leanh::LeanObject,
    mut v_newNames_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNewEqs_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3187_ = l_Lean_Meta_injectionCore(
                    v_mvarId_3179_,
                    v_fvarId_3180_,
                    v_a_3182_,
                    v_a_3183_,
                    v_a_3184_,
                    v_a_3185_,
                );
                if crate::leanh::lean_obj_tag(v___x_3187_) == 0 {
                    v_a_3188_ = crate::leanh::lean_ctor_get(v___x_3187_, 0);
                    v_isSharedCheck_3200_ = (!crate::leanh::lean_is_exclusive(v___x_3187_)) as u8;
                    if v_isSharedCheck_3200_ == 0 {
                        v___x_3190_ = v___x_3187_;
                        v_isShared_3191_ = v_isSharedCheck_3200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3188_);
                        crate::leanh::lean_dec(v___x_3187_);
                        v___x_3190_ = crate::leanh::lean_box(0);
                        v_isShared_3191_ = v_isSharedCheck_3200_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_newNames_3181_);
                    v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3187_, 0);
                    v_isSharedCheck_3208_ = (!crate::leanh::lean_is_exclusive(v___x_3187_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3203_ = v___x_3187_;
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3201_);
                        crate::leanh::lean_dec(v___x_3187_);
                        v___x_3203_ = crate::leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3188_) == 0 {
                    crate::leanh::lean_dec(v_newNames_3181_);
                    v___x_3192_ = crate::leanh::lean_box(0);
                    if v_isShared_3191_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3192_);
                        v___x_3194_ = v___x_3190_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
                        v___x_3194_ = v_reuseFailAlloc_3195_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3190_);
                    v_mvarId_3196_ = crate::leanh::lean_ctor_get(v_a_3188_, 0);
                    crate::leanh::lean_inc(v_mvarId_3196_);
                    v_numNewEqs_3197_ = crate::leanh::lean_ctor_get(v_a_3188_, 1);
                    crate::leanh::lean_inc(v_numNewEqs_3197_);
                    crate::leanh::lean_dec_ref_known(v_a_3188_, 2);
                    v___x_3198_ = 1;
                    v___x_3199_ = l_Lean_Meta_injectionIntro(
                        v_mvarId_3196_,
                        v_numNewEqs_3197_,
                        v_newNames_3181_,
                        v___x_3198_,
                        v_a_3182_,
                        v_a_3183_,
                        v_a_3184_,
                        v_a_3185_,
                    );
                    return v___x_3199_;
                }
            }
            2 => {
                return v___x_3194_;
            }
            3 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_injection___boxed(
    mut v_mvarId_3209_: *mut crate::leanh::LeanObject,
    mut v_fvarId_3210_: *mut crate::leanh::LeanObject,
    mut v_newNames_3211_: *mut crate::leanh::LeanObject,
    mut v_a_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
    mut v_a_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = l_Lean_Meta_injection(
        v_mvarId_3209_,
        v_fvarId_3210_,
        v_newNames_3211_,
        v_a_3212_,
        v_a_3213_,
        v_a_3214_,
        v_a_3215_,
    );
    crate::leanh::lean_dec(v_a_3215_);
    crate::leanh::lean_dec_ref(v_a_3214_);
    crate::leanh::lean_dec(v_a_3213_);
    crate::leanh::lean_dec_ref(v_a_3212_);
    return v_res_3217_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorIdx(
    mut v_x_3218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3218_) == 0 {
        let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3219_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3219_;
    } else {
        let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3220_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3220_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorIdx___boxed(
    mut v_x_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_3221_);
    crate::leanh::lean_dec(v_x_3221_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim___redArg(
    mut v_t_3223_: *mut crate::leanh::LeanObject,
    mut v_k_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3223_) == 0 {
        return v_k_3224_;
    } else {
        let mut v_mvarId_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_remainingNames_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_forbidden_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_3225_ = crate::leanh::lean_ctor_get(v_t_3223_, 0);
        crate::leanh::lean_inc(v_mvarId_3225_);
        v_remainingNames_3226_ = crate::leanh::lean_ctor_get(v_t_3223_, 1);
        crate::leanh::lean_inc(v_remainingNames_3226_);
        v_forbidden_3227_ = crate::leanh::lean_ctor_get(v_t_3223_, 2);
        crate::leanh::lean_inc(v_forbidden_3227_);
        crate::leanh::lean_dec_ref_known(v_t_3223_, 3);
        v___x_3228_ = crate::leanh::lean_apply_3(
            v_k_3224_,
            v_mvarId_3225_,
            v_remainingNames_3226_,
            v_forbidden_3227_,
        );
        return v___x_3228_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim(
    mut v_motive_3229_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3230_: *mut crate::leanh::LeanObject,
    mut v_t_3231_: *mut crate::leanh::LeanObject,
    mut v_h_3232_: *mut crate::leanh::LeanObject,
    mut v_k_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3231_, v_k_3233_);
    return v___x_3234_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim___boxed(
    mut v_motive_3235_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3236_: *mut crate::leanh::LeanObject,
    mut v_t_3237_: *mut crate::leanh::LeanObject,
    mut v_h_3238_: *mut crate::leanh::LeanObject,
    mut v_k_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Meta_InjectionsResult_ctorElim(
        v_motive_3235_,
        v_ctorIdx_3236_,
        v_t_3237_,
        v_h_3238_,
        v_k_3239_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3236_);
    return v_res_3240_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_solved_elim___redArg(
    mut v_t_3241_: *mut crate::leanh::LeanObject,
    mut v_solved_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3241_, v_solved_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_solved_elim(
    mut v_motive_3244_: *mut crate::leanh::LeanObject,
    mut v_t_3245_: *mut crate::leanh::LeanObject,
    mut v_h_3246_: *mut crate::leanh::LeanObject,
    mut v_solved_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3245_, v_solved_3247_);
    return v___x_3248_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(
    mut v_t_3249_: *mut crate::leanh::LeanObject,
    mut v_subgoal_3250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3249_, v_subgoal_3250_);
    return v___x_3251_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_subgoal_elim(
    mut v_motive_3252_: *mut crate::leanh::LeanObject,
    mut v_t_3253_: *mut crate::leanh::LeanObject,
    mut v_h_3254_: *mut crate::leanh::LeanObject,
    mut v_subgoal_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3253_, v_subgoal_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(
    mut v_x_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
    mut v___y_3260_: *mut crate::leanh::LeanObject,
    mut v___y_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut v_unused_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut v_a_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3263_ = l_Lean_Meta_saveState___redArg(v___y_3259_, v___y_3261_);
                if crate::leanh::lean_obj_tag(v___x_3263_) == 0 {
                    v_a_3264_ = crate::leanh::lean_ctor_get(v___x_3263_, 0);
                    crate::leanh::lean_inc(v_a_3264_);
                    crate::leanh::lean_dec_ref_known(v___x_3263_, 1);
                    crate::leanh::lean_inc(v___y_3261_);
                    crate::leanh::lean_inc_ref(v___y_3260_);
                    crate::leanh::lean_inc(v___y_3259_);
                    crate::leanh::lean_inc_ref(v___y_3258_);
                    v___x_3265_ = crate::leanh::lean_apply_5(
                        v_x_3257_,
                        v___y_3258_,
                        v___y_3259_,
                        v___y_3260_,
                        v___y_3261_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3265_) == 0 {
                        crate::leanh::lean_dec(v_a_3264_);
                        return v___x_3265_;
                    } else {
                        v_a_3266_ = crate::leanh::lean_ctor_get(v___x_3265_, 0);
                        crate::leanh::lean_inc(v_a_3266_);
                        v___x_3286_ = l_Lean_Exception_isInterrupt(v_a_3266_);
                        if v___x_3286_ == 0 {
                            crate::leanh::lean_inc(v_a_3266_);
                            v___x_3287_ = l_Lean_Exception_isRuntime(v_a_3266_);
                            v___y_3268_ = v___x_3287_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3268_ = v___x_3286_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_3257_);
                    v_a_3288_ = crate::leanh::lean_ctor_get(v___x_3263_, 0);
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v___x_3263_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3263_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3288_);
                        crate::leanh::lean_dec(v___x_3263_);
                        v___x_3290_ = crate::leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3268_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3265_, 1);
                    v___x_3269_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_3264_,
                        v___y_3259_,
                        v___y_3261_,
                    );
                    crate::leanh::lean_dec(v_a_3264_);
                    if crate::leanh::lean_obj_tag(v___x_3269_) == 0 {
                        v_isSharedCheck_3276_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3269_)) as u8;
                        if v_isSharedCheck_3276_ == 0 {
                            v_unused_3277_ = crate::leanh::lean_ctor_get(v___x_3269_, 0);
                            crate::leanh::lean_dec(v_unused_3277_);
                            v___x_3271_ = v___x_3269_;
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3269_);
                            v___x_3271_ = crate::leanh::lean_box(0);
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3266_);
                        v_a_3278_ = crate::leanh::lean_ctor_get(v___x_3269_, 0);
                        v_isSharedCheck_3285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3269_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3269_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3278_);
                            crate::leanh::lean_dec(v___x_3269_);
                            v___x_3280_ = crate::leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3266_);
                    crate::leanh::lean_dec(v_a_3264_);
                    return v___x_3265_;
                }
            }
            2 => {
                if v_isShared_3272_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3271_, 1);
                    crate::leanh::lean_ctor_set(v___x_3271_, 0, v_a_3266_);
                    v___x_3274_ = v___x_3271_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3266_);
                    v___x_3274_ = v_reuseFailAlloc_3275_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3274_;
            }
            4 => {
                if v_isShared_3281_ == 0 {
                    v___x_3283_ = v___x_3280_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
                    v___x_3283_ = v_reuseFailAlloc_3284_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3283_;
            }
            6 => {
                if v_isShared_3291_ == 0 {
                    v___x_3293_ = v___x_3290_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg___boxed(
    mut v_x_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    crate::leanh::lean_dec(v___y_3300_);
    crate::leanh::lean_dec_ref(v___y_3299_);
    crate::leanh::lean_dec(v___y_3298_);
    crate::leanh::lean_dec_ref(v___y_3297_);
    return v_res_3302_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(
    mut v_00_u03b1_3303_: *mut crate::leanh::LeanObject,
    mut v_x_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
    return v___x_3310_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(
    mut v_00_u03b1_3311_: *mut crate::leanh::LeanObject,
    mut v_x_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3318_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_3311_, v_x_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
    crate::leanh::lean_dec(v___y_3316_);
    crate::leanh::lean_dec_ref(v___y_3315_);
    crate::leanh::lean_dec(v___y_3314_);
    crate::leanh::lean_dec_ref(v___y_3313_);
    return v_res_3318_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(
    mut v_k_3319_: *mut crate::leanh::LeanObject,
    mut v_t_3320_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3320_) == 0 {
                    v_k_3321_ = crate::leanh::lean_ctor_get(v_t_3320_, 1);
                    v_l_3322_ = crate::leanh::lean_ctor_get(v_t_3320_, 3);
                    v_r_3323_ = crate::leanh::lean_ctor_get(v_t_3320_, 4);
                    v___x_3324_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3319_, v_k_3321_);
                    match v___x_3324_ {
                        0 => {
                            v_t_3320_ = v_l_3322_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_3326_ = 1;
                            return v___x_3326_;
                        }
                        _ => {
                            v_t_3320_ = v_r_3323_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3328_ = 0;
                    return v___x_3328_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg___boxed(
    mut v_k_3329_: *mut crate::leanh::LeanObject,
    mut v_t_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: u8 = 0;
    let mut v_r_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_3329_, v_t_3330_);
    crate::leanh::lean_dec(v_t_3330_);
    crate::leanh::lean_dec(v_k_3329_);
    v_r_3332_ = crate::leanh::lean_box((v_res_3331_) as usize);
    return v_r_3332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3;
    v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
    return v___x_3340_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once
        ),
        _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4,
    );
    v___x_3342_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
    return v___x_3342_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(
    mut v_mvarId_3343_: *mut crate::leanh::LeanObject,
    mut v_head_3344_: *mut crate::leanh::LeanObject,
    mut v_newNames_3345_: *mut crate::leanh::LeanObject,
    mut v_tail_3346_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3347_: *mut crate::leanh::LeanObject,
    mut v_n_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3354_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(
        v_mvarId_3343_,
        v_head_3344_,
        v_newNames_3345_,
        v_tail_3346_,
        v_forbidden_3347_,
        v_n_3348_,
        v___y_3349_,
        v___y_3350_,
        v___y_3351_,
        v___y_3352_,
    );
    crate::leanh::lean_dec(v___y_3352_);
    crate::leanh::lean_dec_ref(v___y_3351_);
    crate::leanh::lean_dec(v___y_3350_);
    crate::leanh::lean_dec_ref(v___y_3349_);
    return v_res_3354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(
    mut v_depth_3355_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3356_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3357_: *mut crate::leanh::LeanObject,
    mut v_newNames_3358_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3366_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: u8 = 0;
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: u8 = 0;
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v_a_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3411_: u8 = 0;
    let mut v_a_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3419_: u8 = 0;
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v_a_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3432_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3365_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3366_ = lean_nat_dec_eq(v_depth_3355_, v_zero_3365_);
                if v_isZero_3366_ == 1 {
                    crate::leanh::lean_dec(v_forbidden_3359_);
                    crate::leanh::lean_dec(v_newNames_3358_);
                    crate::leanh::lean_dec(v_fvarIds_3356_);
                    crate::leanh::lean_dec(v_depth_3355_);
                    v___x_3367_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1;
                    v___x_3368_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once), _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
                    v___x_3369_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3367_,
                        v_mvarId_3357_,
                        v___x_3368_,
                        v_a_3360_,
                        v_a_3361_,
                        v_a_3362_,
                        v_a_3363_,
                    );
                    return v___x_3369_;
                } else {
                    if crate::leanh::lean_obj_tag(v_fvarIds_3356_) == 0 {
                        crate::leanh::lean_dec(v_depth_3355_);
                        v___x_3370_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3370_, 0, v_mvarId_3357_);
                        crate::leanh::lean_ctor_set(v___x_3370_, 1, v_newNames_3358_);
                        crate::leanh::lean_ctor_set(v___x_3370_, 2, v_forbidden_3359_);
                        v___x_3371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3371_, 0, v___x_3370_);
                        return v___x_3371_;
                    } else {
                        v_head_3372_ = crate::leanh::lean_ctor_get(v_fvarIds_3356_, 0);
                        crate::leanh::lean_inc(v_head_3372_);
                        v_tail_3373_ = crate::leanh::lean_ctor_get(v_fvarIds_3356_, 1);
                        crate::leanh::lean_inc(v_tail_3373_);
                        crate::leanh::lean_dec_ref_known(v_fvarIds_3356_, 2);
                        v_one_3374_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_3375_ = lean_nat_sub(v_depth_3355_, v_one_3374_);
                        crate::leanh::lean_dec(v_depth_3355_);
                        v___x_3376_ = lean_nat_add(v_n_3375_, v_one_3374_);
                        v___x_3381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_3372_, v_forbidden_3359_);
                        if v___x_3381_ == 0 {
                            crate::leanh::lean_inc(v_head_3372_);
                            v___x_3382_ = l_Lean_FVarId_getType___redArg(
                                v_head_3372_,
                                v_a_3360_,
                                v_a_3362_,
                                v_a_3363_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3382_) == 0 {
                                v_a_3383_ = crate::leanh::lean_ctor_get(v___x_3382_, 0);
                                crate::leanh::lean_inc(v_a_3383_);
                                crate::leanh::lean_dec_ref_known(v___x_3382_, 1);
                                v___x_3384_ = l_Lean_Meta_matchEqHEq_x3f(
                                    v_a_3383_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3384_) == 0 {
                                    v_a_3385_ = crate::leanh::lean_ctor_get(v___x_3384_, 0);
                                    crate::leanh::lean_inc(v_a_3385_);
                                    crate::leanh::lean_dec_ref_known(v___x_3384_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_3385_) == 1 {
                                        v_val_3386_ = crate::leanh::lean_ctor_get(v_a_3385_, 0);
                                        crate::leanh::lean_inc(v_val_3386_);
                                        crate::leanh::lean_dec_ref_known(v_a_3385_, 1);
                                        v_snd_3387_ = crate::leanh::lean_ctor_get(v_val_3386_, 1);
                                        crate::leanh::lean_inc(v_snd_3387_);
                                        crate::leanh::lean_dec(v_val_3386_);
                                        v_fst_3388_ = crate::leanh::lean_ctor_get(v_snd_3387_, 0);
                                        crate::leanh::lean_inc(v_fst_3388_);
                                        v_snd_3389_ = crate::leanh::lean_ctor_get(v_snd_3387_, 1);
                                        crate::leanh::lean_inc(v_snd_3389_);
                                        crate::leanh::lean_dec(v_snd_3387_);
                                        crate::leanh::lean_inc(v_a_3363_);
                                        crate::leanh::lean_inc_ref(v_a_3362_);
                                        crate::leanh::lean_inc(v_a_3361_);
                                        crate::leanh::lean_inc_ref(v_a_3360_);
                                        v___x_3390_ = lean_whnf(
                                            v_fst_3388_,
                                            v_a_3360_,
                                            v_a_3361_,
                                            v_a_3362_,
                                            v_a_3363_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_3390_) == 0 {
                                            v_a_3391_ = crate::leanh::lean_ctor_get(v___x_3390_, 0);
                                            crate::leanh::lean_inc(v_a_3391_);
                                            crate::leanh::lean_dec_ref_known(v___x_3390_, 1);
                                            crate::leanh::lean_inc(v_a_3363_);
                                            crate::leanh::lean_inc_ref(v_a_3362_);
                                            crate::leanh::lean_inc(v_a_3361_);
                                            crate::leanh::lean_inc_ref(v_a_3360_);
                                            v___x_3392_ = lean_whnf(
                                                v_snd_3389_,
                                                v_a_3360_,
                                                v_a_3361_,
                                                v_a_3362_,
                                                v_a_3363_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_3392_) == 0 {
                                                v_a_3393_ =
                                                    crate::leanh::lean_ctor_get(v___x_3392_, 0);
                                                crate::leanh::lean_inc(v_a_3393_);
                                                crate::leanh::lean_dec_ref_known(v___x_3392_, 1);
                                                crate::leanh::lean_inc(v_forbidden_3359_);
                                                crate::leanh::lean_inc(v_tail_3373_);
                                                crate::leanh::lean_inc(v_newNames_3358_);
                                                crate::leanh::lean_inc(v_mvarId_3357_);
                                                v___f_3394_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    0,
                                                    v_mvarId_3357_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    1,
                                                    v_head_3372_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    2,
                                                    v_newNames_3358_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    3,
                                                    v_tail_3373_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    4,
                                                    v_forbidden_3359_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    5,
                                                    v_n_3375_,
                                                );
                                                v___x_3402_ = l_Lean_Expr_isRawNatLit(v_a_3391_);
                                                crate::leanh::lean_dec(v_a_3391_);
                                                if v___x_3402_ == 0 {
                                                    crate::leanh::lean_dec(v_a_3393_);
                                                    v___y_3396_ = v___x_3402_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_3403_ =
                                                        l_Lean_Expr_isRawNatLit(v_a_3393_);
                                                    crate::leanh::lean_dec(v_a_3393_);
                                                    v___y_3396_ = v___x_3403_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_3391_);
                                                crate::leanh::lean_dec(v___x_3376_);
                                                crate::leanh::lean_dec(v_n_3375_);
                                                crate::leanh::lean_dec(v_tail_3373_);
                                                crate::leanh::lean_dec(v_head_3372_);
                                                crate::leanh::lean_dec(v_forbidden_3359_);
                                                crate::leanh::lean_dec(v_newNames_3358_);
                                                crate::leanh::lean_dec(v_mvarId_3357_);
                                                v_a_3404_ =
                                                    crate::leanh::lean_ctor_get(v___x_3392_, 0);
                                                v_isSharedCheck_3411_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3392_))
                                                        as u8;
                                                if v_isSharedCheck_3411_ == 0 {
                                                    v___x_3406_ = v___x_3392_;
                                                    v_isShared_3407_ = v_isSharedCheck_3411_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3404_);
                                                    crate::leanh::lean_dec(v___x_3392_);
                                                    v___x_3406_ = crate::leanh::lean_box(0);
                                                    v_isShared_3407_ = v_isSharedCheck_3411_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_snd_3389_);
                                            crate::leanh::lean_dec(v___x_3376_);
                                            crate::leanh::lean_dec(v_n_3375_);
                                            crate::leanh::lean_dec(v_tail_3373_);
                                            crate::leanh::lean_dec(v_head_3372_);
                                            crate::leanh::lean_dec(v_forbidden_3359_);
                                            crate::leanh::lean_dec(v_newNames_3358_);
                                            crate::leanh::lean_dec(v_mvarId_3357_);
                                            v_a_3412_ = crate::leanh::lean_ctor_get(v___x_3390_, 0);
                                            v_isSharedCheck_3419_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3390_))
                                                    as u8;
                                            if v_isSharedCheck_3419_ == 0 {
                                                v___x_3414_ = v___x_3390_;
                                                v_isShared_3415_ = v_isSharedCheck_3419_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3412_);
                                                crate::leanh::lean_dec(v___x_3390_);
                                                v___x_3414_ = crate::leanh::lean_box(0);
                                                v_isShared_3415_ = v_isSharedCheck_3419_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3385_);
                                        crate::leanh::lean_dec(v_n_3375_);
                                        crate::leanh::lean_dec(v_head_3372_);
                                        v_depth_3355_ = v___x_3376_;
                                        v_fvarIds_3356_ = v_tail_3373_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_3376_);
                                    crate::leanh::lean_dec(v_n_3375_);
                                    crate::leanh::lean_dec(v_tail_3373_);
                                    crate::leanh::lean_dec(v_head_3372_);
                                    crate::leanh::lean_dec(v_forbidden_3359_);
                                    crate::leanh::lean_dec(v_newNames_3358_);
                                    crate::leanh::lean_dec(v_mvarId_3357_);
                                    v_a_3421_ = crate::leanh::lean_ctor_get(v___x_3384_, 0);
                                    v_isSharedCheck_3428_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3384_)) as u8;
                                    if v_isSharedCheck_3428_ == 0 {
                                        v___x_3423_ = v___x_3384_;
                                        v_isShared_3424_ = v_isSharedCheck_3428_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3421_);
                                        crate::leanh::lean_dec(v___x_3384_);
                                        v___x_3423_ = crate::leanh::lean_box(0);
                                        v_isShared_3424_ = v_isSharedCheck_3428_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_3376_);
                                crate::leanh::lean_dec(v_n_3375_);
                                crate::leanh::lean_dec(v_tail_3373_);
                                crate::leanh::lean_dec(v_head_3372_);
                                crate::leanh::lean_dec(v_forbidden_3359_);
                                crate::leanh::lean_dec(v_newNames_3358_);
                                crate::leanh::lean_dec(v_mvarId_3357_);
                                v_a_3429_ = crate::leanh::lean_ctor_get(v___x_3382_, 0);
                                v_isSharedCheck_3436_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3382_)) as u8;
                                if v_isSharedCheck_3436_ == 0 {
                                    v___x_3431_ = v___x_3382_;
                                    v_isShared_3432_ = v_isSharedCheck_3436_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3429_);
                                    crate::leanh::lean_dec(v___x_3382_);
                                    v___x_3431_ = crate::leanh::lean_box(0);
                                    v_isShared_3432_ = v_isSharedCheck_3436_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_n_3375_);
                            crate::leanh::lean_dec(v_head_3372_);
                            v_depth_3355_ = v___x_3376_;
                            v_fvarIds_3356_ = v_tail_3373_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_3379_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3378_);
                    v_depth_3355_ = v___x_3376_;
                    v_fvarIds_3356_ = v_tail_3373_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3376_);
                    crate::leanh::lean_dec(v_tail_3373_);
                    crate::leanh::lean_dec(v_forbidden_3359_);
                    crate::leanh::lean_dec(v_newNames_3358_);
                    crate::leanh::lean_dec(v_mvarId_3357_);
                    return v___y_3378_;
                }
            }
            2 => {
                if v___y_3396_ == 0 {
                    v___x_3397_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_3394_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
                    if crate::leanh::lean_obj_tag(v___x_3397_) == 0 {
                        crate::leanh::lean_dec(v___x_3376_);
                        crate::leanh::lean_dec(v_tail_3373_);
                        crate::leanh::lean_dec(v_forbidden_3359_);
                        crate::leanh::lean_dec(v_newNames_3358_);
                        crate::leanh::lean_dec(v_mvarId_3357_);
                        return v___x_3397_;
                    } else {
                        v_a_3398_ = crate::leanh::lean_ctor_get(v___x_3397_, 0);
                        crate::leanh::lean_inc(v_a_3398_);
                        v___x_3399_ = l_Lean_Exception_isInterrupt(v_a_3398_);
                        if v___x_3399_ == 0 {
                            v___x_3400_ = l_Lean_Exception_isRuntime(v_a_3398_);
                            v___y_3378_ = v___x_3397_;
                            v___y_3379_ = v___x_3400_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3398_);
                            v___y_3378_ = v___x_3397_;
                            v___y_3379_ = v___x_3399_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_3394_);
                    v_depth_3355_ = v___x_3376_;
                    v_fvarIds_3356_ = v_tail_3373_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                if v_isShared_3407_ == 0 {
                    v___x_3409_ = v___x_3406_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
                    v___x_3409_ = v_reuseFailAlloc_3410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3409_;
            }
            5 => {
                if v_isShared_3415_ == 0 {
                    v___x_3417_ = v___x_3414_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
                    v___x_3417_ = v_reuseFailAlloc_3418_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3417_;
            }
            7 => {
                if v_isShared_3424_ == 0 {
                    v___x_3426_ = v___x_3423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
                    v___x_3426_ = v_reuseFailAlloc_3427_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3426_;
            }
            9 => {
                if v_isShared_3432_ == 0 {
                    v___x_3434_ = v___x_3431_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
                    v___x_3434_ = v_reuseFailAlloc_3435_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed(
    mut v_depth_3438_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_3439_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3440_: *mut crate::leanh::LeanObject,
    mut v_newNames_3441_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(
        v_depth_3438_,
        v_fvarIds_3439_,
        v_mvarId_3440_,
        v_newNames_3441_,
        v_forbidden_3442_,
        v_a_3443_,
        v_a_3444_,
        v_a_3445_,
        v_a_3446_,
    );
    crate::leanh::lean_dec(v_a_3446_);
    crate::leanh::lean_dec_ref(v_a_3445_);
    crate::leanh::lean_dec(v_a_3444_);
    crate::leanh::lean_dec_ref(v_a_3443_);
    return v_res_3448_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(
    mut v_mvarId_3449_: *mut crate::leanh::LeanObject,
    mut v_head_3450_: *mut crate::leanh::LeanObject,
    mut v_newNames_3451_: *mut crate::leanh::LeanObject,
    mut v_tail_3452_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3453_: *mut crate::leanh::LeanObject,
    mut v_n_3454_: *mut crate::leanh::LeanObject,
    mut v___y_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEqs_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_a_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_head_3450_);
                v___x_3460_ = l_Lean_Meta_injection(
                    v_mvarId_3449_,
                    v_head_3450_,
                    v_newNames_3451_,
                    v___y_3455_,
                    v___y_3456_,
                    v___y_3457_,
                    v___y_3458_,
                );
                if crate::leanh::lean_obj_tag(v___x_3460_) == 0 {
                    v_a_3461_ = crate::leanh::lean_ctor_get(v___x_3460_, 0);
                    v_isSharedCheck_3477_ = (!crate::leanh::lean_is_exclusive(v___x_3460_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3463_ = v___x_3460_;
                        v_isShared_3464_ = v_isSharedCheck_3477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3461_);
                        crate::leanh::lean_dec(v___x_3460_);
                        v___x_3463_ = crate::leanh::lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3477_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_3454_);
                    crate::leanh::lean_dec(v_forbidden_3453_);
                    crate::leanh::lean_dec(v_tail_3452_);
                    crate::leanh::lean_dec(v_head_3450_);
                    v_a_3478_ = crate::leanh::lean_ctor_get(v___x_3460_, 0);
                    v_isSharedCheck_3485_ = (!crate::leanh::lean_is_exclusive(v___x_3460_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3480_ = v___x_3460_;
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3478_);
                        crate::leanh::lean_dec(v___x_3460_);
                        v___x_3480_ = crate::leanh::lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3461_) == 0 {
                    crate::leanh::lean_dec(v_n_3454_);
                    crate::leanh::lean_dec(v_forbidden_3453_);
                    crate::leanh::lean_dec(v_tail_3452_);
                    crate::leanh::lean_dec(v_head_3450_);
                    v___x_3465_ = crate::leanh::lean_box(0);
                    if v_isShared_3464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3465_);
                        v___x_3467_ = v___x_3463_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3463_);
                    v_mvarId_3469_ = crate::leanh::lean_ctor_get(v_a_3461_, 0);
                    crate::leanh::lean_inc_n(v_mvarId_3469_, 2);
                    v_newEqs_3470_ = crate::leanh::lean_ctor_get(v_a_3461_, 1);
                    crate::leanh::lean_inc_ref(v_newEqs_3470_);
                    v_remainingNames_3471_ = crate::leanh::lean_ctor_get(v_a_3461_, 2);
                    crate::leanh::lean_inc(v_remainingNames_3471_);
                    crate::leanh::lean_dec_ref_known(v_a_3461_, 3);
                    v___x_3472_ = lean_array_to_list(v_newEqs_3470_);
                    v___x_3473_ = l_List_appendTR___redArg(v___x_3472_, v_tail_3452_);
                    v___x_3474_ = l_Lean_FVarIdSet_insert(v_forbidden_3453_, v_head_3450_);
                    v___x_3475_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___x_3475_, 0, v_n_3454_);
                    crate::leanh::lean_closure_set(v___x_3475_, 1, v___x_3473_);
                    crate::leanh::lean_closure_set(v___x_3475_, 2, v_mvarId_3469_);
                    crate::leanh::lean_closure_set(v___x_3475_, 3, v_remainingNames_3471_);
                    crate::leanh::lean_closure_set(v___x_3475_, 4, v___x_3474_);
                    v___x_3476_ =
                        l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
                            v_mvarId_3469_,
                            v___x_3475_,
                            v___y_3455_,
                            v___y_3456_,
                            v___y_3457_,
                            v___y_3458_,
                        );
                    return v___x_3476_;
                }
            }
            2 => {
                return v___x_3467_;
            }
            3 => {
                if v_isShared_3481_ == 0 {
                    v___x_3483_ = v___x_3480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(
    mut v_00_u03b2_3486_: *mut crate::leanh::LeanObject,
    mut v_k_3487_: *mut crate::leanh::LeanObject,
    mut v_t_3488_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3489_: u8 = 0;
    v___x_3489_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_3487_, v_t_3488_);
    return v___x_3489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(
    mut v_00_u03b2_3490_: *mut crate::leanh::LeanObject,
    mut v_k_3491_: *mut crate::leanh::LeanObject,
    mut v_t_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3493_: u8 = 0;
    let mut v_r_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_3490_, v_k_3491_, v_t_3492_);
    crate::leanh::lean_dec(v_t_3492_);
    crate::leanh::lean_dec(v_k_3491_);
    v_r_3494_ = crate::leanh::lean_box((v_res_3493_) as usize);
    return v_r_3494_;
}
pub unsafe fn l_Lean_Meta_injections___lam__0(
    mut v_maxDepth_3495_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3496_: *mut crate::leanh::LeanObject,
    mut v_newNames_3497_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3504_ = crate::leanh::lean_ctor_get(v___y_3499_, 2);
    v___x_3505_ = l_Lean_LocalContext_getFVarIds(v_lctx_3504_);
    v___x_3506_ = lean_array_to_list(v___x_3505_);
    v___x_3507_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(
        v_maxDepth_3495_,
        v___x_3506_,
        v_mvarId_3496_,
        v_newNames_3497_,
        v_forbidden_3498_,
        v___y_3499_,
        v___y_3500_,
        v___y_3501_,
        v___y_3502_,
    );
    return v___x_3507_;
}
pub unsafe fn l_Lean_Meta_injections___lam__0___boxed(
    mut v_maxDepth_3508_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3509_: *mut crate::leanh::LeanObject,
    mut v_newNames_3510_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
    mut v___y_3516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3517_ = l_Lean_Meta_injections___lam__0(
        v_maxDepth_3508_,
        v_mvarId_3509_,
        v_newNames_3510_,
        v_forbidden_3511_,
        v___y_3512_,
        v___y_3513_,
        v___y_3514_,
        v___y_3515_,
    );
    crate::leanh::lean_dec(v___y_3515_);
    crate::leanh::lean_dec_ref(v___y_3514_);
    crate::leanh::lean_dec(v___y_3513_);
    crate::leanh::lean_dec_ref(v___y_3512_);
    return v_res_3517_;
}
pub unsafe fn l_Lean_Meta_injections(
    mut v_mvarId_3518_: *mut crate::leanh::LeanObject,
    mut v_newNames_3519_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_3520_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_3518_);
    v___f_3527_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_injections___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_3527_, 0, v_maxDepth_3520_);
    crate::leanh::lean_closure_set(v___f_3527_, 1, v_mvarId_3518_);
    crate::leanh::lean_closure_set(v___f_3527_, 2, v_newNames_3519_);
    crate::leanh::lean_closure_set(v___f_3527_, 3, v_forbidden_3521_);
    v___x_3528_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
        v_mvarId_3518_,
        v___f_3527_,
        v_a_3522_,
        v_a_3523_,
        v_a_3524_,
        v_a_3525_,
    );
    return v___x_3528_;
}
pub unsafe fn l_Lean_Meta_injections___boxed(
    mut v_mvarId_3529_: *mut crate::leanh::LeanObject,
    mut v_newNames_3530_: *mut crate::leanh::LeanObject,
    mut v_maxDepth_3531_: *mut crate::leanh::LeanObject,
    mut v_forbidden_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_a_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_Meta_injections(
        v_mvarId_3529_,
        v_newNames_3530_,
        v_maxDepth_3531_,
        v_forbidden_3532_,
        v_a_3533_,
        v_a_3534_,
        v_a_3535_,
        v_a_3536_,
    );
    crate::leanh::lean_dec(v_a_3536_);
    crate::leanh::lean_dec_ref(v_a_3535_);
    crate::leanh::lean_dec(v_a_3534_);
    crate::leanh::lean_dec_ref(v_a_3533_);
    return v_res_3538_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_Meta_injectionIntro___closed__1;
    v___x_3596_ = 0;
    v___x_3597_ = l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_;
    v___x_3598_ = l_Lean_registerTraceClass(v___x_3595_, v___x_3596_, v___x_3597_);
    return v___x_3598_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(
    mut v_a_3599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
    return v_res_3600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Injection(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Injection(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Injection(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Injection(builtin);
}
