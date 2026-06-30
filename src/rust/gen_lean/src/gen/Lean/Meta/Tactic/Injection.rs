// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Lean.Meta.Tactic.Subst
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_infer_type, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr3};
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
pub static l_Lean_Meta_injectionCore___lam__0___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_injectionCore___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__0_value: leanh::LeanStringObject<
    46,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__4_value: leanh::LeanStringObject<
    46,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__8_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__10_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__12_value: leanh::LeanStringObject<
    57,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__14: u64 = 0;
pub static l_Lean_Meta_injectionCore___lam__1___closed__15_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__17_value: leanh::LeanStringObject<
    9,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__19_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__19_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__21_value: leanh::LeanStringObject<
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
        101, 113, 117, 97, 108, 105, 116, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__22_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_injectionCore___lam__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__25_value: leanh::LeanStringObject<
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__26_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__27_value: leanh::LeanStringObject<
    25,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__29_value: leanh::LeanStringObject<
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
    m_data: [32, 97, 116, 10, 0],
};
static mut l_Lean_Meta_injectionCore___lam__1___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionCore___lam__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionCore___lam__1___closed__31_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___lam__1___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___lam__1___closed__32_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__31_value)
                as *mut leanh::LeanObject,
            13589827700912665667 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___lam__1___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionCore___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
                as *mut leanh::LeanObject,
            12874249535713742015 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_injectionIntro___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_injectionIntro___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_injectionIntro___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value)
                as *mut leanh::LeanObject,
            142734480563613395 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_injectionIntro___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value)
                as *mut leanh::LeanObject,
            15847151208953044930 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_injectionIntro___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_injectionCore___closed__0_value)
                as *mut leanh::LeanObject,
            12445953579901931010 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_injectionIntro___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionIntro___closed__3_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionIntro___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_injectionIntro___closed__5_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_injectionIntro___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_injectionIntro___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_injectionIntro___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_injectionIntro___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value:
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
    m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__0_value
        ) as *mut leanh::LeanObject,
        5163565424560827901 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__0_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__1_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__3_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__4_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__5_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2197290662802231936 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__7_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,223750332802285625 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__8_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__9_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16461794931444949472 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__10_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__11_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13255495822366105665 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__12_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__2_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,244446394462504164 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__13_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__25_value) as *mut leanh::LeanObject,4458521110757701240 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__14_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_injectionCore___lam__1___closed__26_value) as *mut leanh::LeanObject,4208024077724612965 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__15_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__6_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17090328229070726430 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__16_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1583609249 as usize) << 1) | 1) as *mut leanh::LeanObject,4074967462205855788 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__17_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__18_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16020934614818583779 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__19_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__20_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6029258889307722371 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__21_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,6712643992094006598 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(
    mut v_k_1801_: *mut leanh::LeanObject,
    mut v_b_1802_: *mut leanh::LeanObject,
    mut v_c_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1807_);
    leanh::lean_inc_ref(v___y_1806_);
    leanh::lean_inc(v___y_1805_);
    leanh::lean_inc_ref(v___y_1804_);
    v___x_1809_ = leanh::lean_apply_7(
        v_k_1801_,
        v_b_1802_,
        v_c_1803_,
        v___y_1804_,
        v___y_1805_,
        v___y_1806_,
        v___y_1807_,
        leanh::lean_box(0),
    );
    return v___x_1809_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed(
    mut v_k_1810_: *mut leanh::LeanObject,
    mut v_b_1811_: *mut leanh::LeanObject,
    mut v_c_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0(v_k_1810_, v_b_1811_, v_c_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    leanh::lean_dec(v___y_1816_);
    leanh::lean_dec_ref(v___y_1815_);
    leanh::lean_dec(v___y_1814_);
    leanh::lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(
    mut v_type_1819_: *mut leanh::LeanObject,
    mut v_k_1820_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1821_: u8,
    mut v_whnfType_1822_: u8,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1833_: u8 = 0;
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1837_: u8 = 0;
    let mut v_a_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1841_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1828_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1828_, 0, v_k_1820_);
                v___x_1829_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_1819_,
                    v___f_1828_,
                    v_cleanupAnnotations_1821_,
                    v_whnfType_1822_,
                    v___y_1823_,
                    v___y_1824_,
                    v___y_1825_,
                    v___y_1826_,
                );
                if leanh::lean_obj_tag(v___x_1829_) == 0 {
                    v_a_1830_ = leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1837_ = (!leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1837_ == 0 {
                        v___x_1832_ = v___x_1829_;
                        v_isShared_1833_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1830_);
                        leanh::lean_dec(v___x_1829_);
                        v___x_1832_ = leanh::lean_box(0);
                        v_isShared_1833_ = v_isSharedCheck_1837_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1838_ = leanh::lean_ctor_get(v___x_1829_, 0);
                    v_isSharedCheck_1845_ = (!leanh::lean_is_exclusive(v___x_1829_)) as u8;
                    if v_isSharedCheck_1845_ == 0 {
                        v___x_1840_ = v___x_1829_;
                        v_isShared_1841_ = v_isSharedCheck_1845_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1838_);
                        leanh::lean_dec(v___x_1829_);
                        v___x_1840_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1836_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
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
                    v_reuseFailAlloc_1844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
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
    mut v_type_1846_: *mut leanh::LeanObject,
    mut v_k_1847_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1848_: *mut leanh::LeanObject,
    mut v_whnfType_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1855_: u8 = 0;
    let mut v_whnfType_boxed_1856_: u8 = 0;
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1855_ = (leanh::lean_unbox(v_cleanupAnnotations_1848_) as u8);
    v_whnfType_boxed_1856_ = (leanh::lean_unbox(v_whnfType_1849_) as u8);
    v_res_1857_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1846_, v_k_1847_, v_cleanupAnnotations_boxed_1855_, v_whnfType_boxed_1856_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
    leanh::lean_dec(v___y_1853_);
    leanh::lean_dec_ref(v___y_1852_);
    leanh::lean_dec(v___y_1851_);
    leanh::lean_dec_ref(v___y_1850_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1(
    mut v_00_u03b1_1858_: *mut leanh::LeanObject,
    mut v_type_1859_: *mut leanh::LeanObject,
    mut v_k_1860_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1861_: u8,
    mut v_whnfType_1862_: u8,
    mut v___y_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1859_, v_k_1860_, v_cleanupAnnotations_1861_, v_whnfType_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___boxed(
    mut v_00_u03b1_1869_: *mut leanh::LeanObject,
    mut v_type_1870_: *mut leanh::LeanObject,
    mut v_k_1871_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1872_: *mut leanh::LeanObject,
    mut v_whnfType_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1879_: u8 = 0;
    let mut v_whnfType_boxed_1880_: u8 = 0;
    let mut v_res_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1879_ = (leanh::lean_unbox(v_cleanupAnnotations_1872_) as u8);
    v_whnfType_boxed_1880_ = (leanh::lean_unbox(v_whnfType_1873_) as u8);
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
    leanh::lean_dec(v___y_1877_);
    leanh::lean_dec_ref(v___y_1876_);
    leanh::lean_dec(v___y_1875_);
    leanh::lean_dec_ref(v___y_1874_);
    return v_res_1881_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0___redArg(
    mut v_upperBound_1882_: *mut leanh::LeanObject,
    mut v_ctorInfo_1883_: *mut leanh::LeanObject,
    mut v_xs_1884_: *mut leanh::LeanObject,
    mut v_a_1885_: *mut leanh::LeanObject,
    mut v_b_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1921_: u8 = 0;
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1892_ = lean_nat_dec_lt(v_a_1885_, v_upperBound_1882_);
                if v___x_1892_ == 0 {
                    leanh::lean_dec(v_a_1885_);
                    v___x_1893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1893_, 0, v_b_1886_);
                    return v___x_1893_;
                } else {
                    v_numParams_1894_ = leanh::lean_ctor_get(v_ctorInfo_1883_, 3);
                    v___x_1895_ = l_Lean_instInhabitedExpr;
                    v___x_1896_ = lean_nat_add(v_numParams_1894_, v_a_1885_);
                    v___x_1897_ = lean_array_get_borrowed(v___x_1895_, v_xs_1884_, v___x_1896_);
                    leanh::lean_dec(v___x_1896_);
                    leanh::lean_inc(v___y_1890_);
                    leanh::lean_inc_ref(v___y_1889_);
                    leanh::lean_inc(v___y_1888_);
                    leanh::lean_inc_ref(v___y_1887_);
                    leanh::lean_inc(v___x_1897_);
                    v___x_1898_ = lean_infer_type(
                        v___x_1897_,
                        v___y_1887_,
                        v___y_1888_,
                        v___y_1889_,
                        v___y_1890_,
                    );
                    if leanh::lean_obj_tag(v___x_1898_) == 0 {
                        v_a_1899_ = leanh::lean_ctor_get(v___x_1898_, 0);
                        leanh::lean_inc(v_a_1899_);
                        leanh::lean_dec_ref_known(v___x_1898_, 1);
                        v___x_1900_ = l_Lean_Meta_isProp(
                            v_a_1899_,
                            v___y_1887_,
                            v___y_1888_,
                            v___y_1889_,
                            v___y_1890_,
                        );
                        if leanh::lean_obj_tag(v___x_1900_) == 0 {
                            v_a_1901_ = leanh::lean_ctor_get(v___x_1900_, 0);
                            leanh::lean_inc(v_a_1901_);
                            leanh::lean_dec_ref_known(v___x_1900_, 1);
                            v___x_1907_ = (leanh::lean_unbox(v_a_1901_) as u8);
                            leanh::lean_dec(v_a_1901_);
                            if v___x_1907_ == 0 {
                                v_a_1903_ = v_b_1886_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1908_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1909_ = lean_nat_add(v_b_1886_, v___x_1908_);
                                leanh::lean_dec(v_b_1886_);
                                v_a_1903_ = v___x_1909_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_b_1886_);
                            leanh::lean_dec(v_a_1885_);
                            v_a_1910_ = leanh::lean_ctor_get(v___x_1900_, 0);
                            v_isSharedCheck_1917_ =
                                (!leanh::lean_is_exclusive(v___x_1900_)) as u8;
                            if v_isSharedCheck_1917_ == 0 {
                                v___x_1912_ = v___x_1900_;
                                v_isShared_1913_ = v_isSharedCheck_1917_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1910_);
                                leanh::lean_dec(v___x_1900_);
                                v___x_1912_ = leanh::lean_box(0);
                                v_isShared_1913_ = v_isSharedCheck_1917_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_b_1886_);
                        leanh::lean_dec(v_a_1885_);
                        v_a_1918_ = leanh::lean_ctor_get(v___x_1898_, 0);
                        v_isSharedCheck_1925_ =
                            (!leanh::lean_is_exclusive(v___x_1898_)) as u8;
                        if v_isSharedCheck_1925_ == 0 {
                            v___x_1920_ = v___x_1898_;
                            v_isShared_1921_ = v_isSharedCheck_1925_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1918_);
                            leanh::lean_dec(v___x_1898_);
                            v___x_1920_ = leanh::lean_box(0);
                            v_isShared_1921_ = v_isSharedCheck_1925_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1904_ = leanh::lean_unsigned_to_nat(1);
                v___x_1905_ = lean_nat_add(v_a_1885_, v___x_1904_);
                leanh::lean_dec(v_a_1885_);
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
                    v_reuseFailAlloc_1916_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
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
                    v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
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
    mut v_upperBound_1926_: *mut leanh::LeanObject,
    mut v_ctorInfo_1927_: *mut leanh::LeanObject,
    mut v_xs_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
    mut v_b_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
    mut v___y_1935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1934_);
    leanh::lean_dec_ref(v___y_1933_);
    leanh::lean_dec(v___y_1932_);
    leanh::lean_dec_ref(v___y_1931_);
    leanh::lean_dec_ref(v_xs_1928_);
    leanh::lean_dec_ref(v_ctorInfo_1927_);
    leanh::lean_dec(v_upperBound_1926_);
    return v_res_1936_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields___lam__0(
    mut v_numFields_1937_: *mut leanh::LeanObject,
    mut v_ctorInfo_1938_: *mut leanh::LeanObject,
    mut v_xs_1939_: *mut leanh::LeanObject,
    mut v_x_1940_: *mut leanh::LeanObject,
    mut v___y_1941_: *mut leanh::LeanObject,
    mut v___y_1942_: *mut leanh::LeanObject,
    mut v___y_1943_: *mut leanh::LeanObject,
    mut v___y_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_numFields_1948_: *mut leanh::LeanObject,
    mut v_ctorInfo_1949_: *mut leanh::LeanObject,
    mut v_xs_1950_: *mut leanh::LeanObject,
    mut v_x_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1955_);
    leanh::lean_dec_ref(v___y_1954_);
    leanh::lean_dec(v___y_1953_);
    leanh::lean_dec_ref(v___y_1952_);
    leanh::lean_dec_ref(v_x_1951_);
    leanh::lean_dec_ref(v_xs_1950_);
    leanh::lean_dec_ref(v_ctorInfo_1949_);
    leanh::lean_dec(v_numFields_1948_);
    return v_res_1957_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields(
    mut v_ctorInfo_1958_: *mut leanh::LeanObject,
    mut v_a_1959_: *mut leanh::LeanObject,
    mut v_a_1960_: *mut leanh::LeanObject,
    mut v_a_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toConstantVal_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_1964_ = leanh::lean_ctor_get(v_ctorInfo_1958_, 0);
    v_numFields_1965_ = leanh::lean_ctor_get(v_ctorInfo_1958_, 4);
    leanh::lean_inc(v_numFields_1965_);
    v_type_1966_ = leanh::lean_ctor_get(v_toConstantVal_1964_, 2);
    leanh::lean_inc_ref(v_type_1966_);
    v___f_1967_ = leanh::lean_alloc_closure(
        l_Lean_Meta_getCtorNumPropFields___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_1967_, 0, v_numFields_1965_);
    leanh::lean_closure_set(v___f_1967_, 1, v_ctorInfo_1958_);
    v___x_1968_ = 0;
    v___x_1969_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getCtorNumPropFields_spec__1___redArg(v_type_1966_, v___f_1967_, v___x_1968_, v___x_1968_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
    return v___x_1969_;
}
pub unsafe fn l_Lean_Meta_getCtorNumPropFields___boxed(
    mut v_ctorInfo_1970_: *mut leanh::LeanObject,
    mut v_a_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_Meta_getCtorNumPropFields(
        v_ctorInfo_1970_,
        v_a_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
    );
    leanh::lean_dec(v_a_1974_);
    leanh::lean_dec_ref(v_a_1973_);
    leanh::lean_dec(v_a_1972_);
    leanh::lean_dec_ref(v_a_1971_);
    return v_res_1976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_getCtorNumPropFields_spec__0(
    mut v_upperBound_1977_: *mut leanh::LeanObject,
    mut v_ctorInfo_1978_: *mut leanh::LeanObject,
    mut v_xs_1979_: *mut leanh::LeanObject,
    mut v_inst_1980_: *mut leanh::LeanObject,
    mut v_R_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
    mut v_b_1983_: *mut leanh::LeanObject,
    mut v_c_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_upperBound_1991_: *mut leanh::LeanObject,
    mut v_ctorInfo_1992_: *mut leanh::LeanObject,
    mut v_xs_1993_: *mut leanh::LeanObject,
    mut v_inst_1994_: *mut leanh::LeanObject,
    mut v_R_1995_: *mut leanh::LeanObject,
    mut v_a_1996_: *mut leanh::LeanObject,
    mut v_b_1997_: *mut leanh::LeanObject,
    mut v_c_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2002_);
    leanh::lean_dec_ref(v___y_2001_);
    leanh::lean_dec(v___y_2000_);
    leanh::lean_dec_ref(v___y_1999_);
    leanh::lean_dec_ref(v_xs_1993_);
    leanh::lean_dec_ref(v_ctorInfo_1992_);
    leanh::lean_dec(v_upperBound_1991_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorIdx(
    mut v_x_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2005_) == 0 {
        let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2006_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2006_;
    } else {
        let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2007_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2007_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorIdx___boxed(
    mut v_x_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_Meta_InjectionResultCore_ctorIdx(v_x_2008_);
    leanh::lean_dec(v_x_2008_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim___redArg(
    mut v_t_2010_: *mut leanh::LeanObject,
    mut v_k_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2010_) == 0 {
        return v_k_2011_;
    } else {
        let mut v_mvarId_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numNewEqs_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_2012_ = leanh::lean_ctor_get(v_t_2010_, 0);
        leanh::lean_inc(v_mvarId_2012_);
        v_numNewEqs_2013_ = leanh::lean_ctor_get(v_t_2010_, 1);
        leanh::lean_inc(v_numNewEqs_2013_);
        leanh::lean_dec_ref_known(v_t_2010_, 2);
        v___x_2014_ = leanh::lean_apply_2(v_k_2011_, v_mvarId_2012_, v_numNewEqs_2013_);
        return v___x_2014_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim(
    mut v_motive_2015_: *mut leanh::LeanObject,
    mut v_ctorIdx_2016_: *mut leanh::LeanObject,
    mut v_t_2017_: *mut leanh::LeanObject,
    mut v_h_2018_: *mut leanh::LeanObject,
    mut v_k_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2017_, v_k_2019_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_ctorElim___boxed(
    mut v_motive_2021_: *mut leanh::LeanObject,
    mut v_ctorIdx_2022_: *mut leanh::LeanObject,
    mut v_t_2023_: *mut leanh::LeanObject,
    mut v_h_2024_: *mut leanh::LeanObject,
    mut v_k_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_Lean_Meta_InjectionResultCore_ctorElim(
        v_motive_2021_,
        v_ctorIdx_2022_,
        v_t_2023_,
        v_h_2024_,
        v_k_2025_,
    );
    leanh::lean_dec(v_ctorIdx_2022_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_solved_elim___redArg(
    mut v_t_2027_: *mut leanh::LeanObject,
    mut v_solved_2028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2027_, v_solved_2028_);
    return v___x_2029_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_solved_elim(
    mut v_motive_2030_: *mut leanh::LeanObject,
    mut v_t_2031_: *mut leanh::LeanObject,
    mut v_h_2032_: *mut leanh::LeanObject,
    mut v_solved_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2031_, v_solved_2033_);
    return v___x_2034_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_subgoal_elim___redArg(
    mut v_t_2035_: *mut leanh::LeanObject,
    mut v_subgoal_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2037_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2035_, v_subgoal_2036_);
    return v___x_2037_;
}
pub unsafe fn l_Lean_Meta_InjectionResultCore_subgoal_elim(
    mut v_motive_2038_: *mut leanh::LeanObject,
    mut v_t_2039_: *mut leanh::LeanObject,
    mut v_h_2040_: *mut leanh::LeanObject,
    mut v_subgoal_2041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Lean_Meta_InjectionResultCore_ctorElim___redArg(v_t_2039_, v_subgoal_2041_);
    return v___x_2042_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
    mut v_mvarId_2043_: *mut leanh::LeanObject,
    mut v_x_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2050_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2043_,
                    v_x_2044_,
                    v___y_2045_,
                    v___y_2046_,
                    v___y_2047_,
                    v___y_2048_,
                );
                if leanh::lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2050_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2051_);
                        leanh::lean_dec(v___x_2050_);
                        v___x_2053_ = leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2059_ = leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2066_ = (!leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2066_ == 0 {
                        v___x_2061_ = v___x_2050_;
                        v_isShared_2062_ = v_isSharedCheck_2066_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2059_);
                        leanh::lean_dec(v___x_2050_);
                        v___x_2061_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
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
                    v_reuseFailAlloc_2065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
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
    mut v_mvarId_2067_: *mut leanh::LeanObject,
    mut v_x_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
    mut v___y_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2074_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2___redArg(
        v_mvarId_2067_,
        v_x_2068_,
        v___y_2069_,
        v___y_2070_,
        v___y_2071_,
        v___y_2072_,
    );
    leanh::lean_dec(v___y_2072_);
    leanh::lean_dec_ref(v___y_2071_);
    leanh::lean_dec(v___y_2070_);
    leanh::lean_dec_ref(v___y_2069_);
    return v_res_2074_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(
    mut v_00_u03b1_2075_: *mut leanh::LeanObject,
    mut v_mvarId_2076_: *mut leanh::LeanObject,
    mut v_x_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2084_: *mut leanh::LeanObject,
    mut v_mvarId_2085_: *mut leanh::LeanObject,
    mut v_x_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
    mut v___y_2090_: *mut leanh::LeanObject,
    mut v___y_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lean_MVarId_withContext___at___00Lean_Meta_injectionCore_spec__2(
        v_00_u03b1_2084_,
        v_mvarId_2085_,
        v_x_2086_,
        v___y_2087_,
        v___y_2088_,
        v___y_2089_,
        v___y_2090_,
    );
    leanh::lean_dec(v___y_2090_);
    leanh::lean_dec_ref(v___y_2089_);
    leanh::lean_dec(v___y_2088_);
    leanh::lean_dec_ref(v___y_2087_);
    return v_res_2092_;
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__0(
    mut v___x_2096_: *mut leanh::LeanObject,
    mut v___y_2097_: *mut leanh::LeanObject,
    mut v___y_2098_: *mut leanh::LeanObject,
    mut v___y_2099_: *mut leanh::LeanObject,
    mut v___y_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2103_: u8 = 0;
    v_options_2102_ = leanh::lean_ctor_get(v___y_2099_, 2);
    v_hasTrace_2103_ = leanh::lean_ctor_get_uint8(
        v_options_2102_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_2103_ == 0 {
        let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_2096_);
        v___x_2104_ = leanh::lean_box((v_hasTrace_2103_) as usize);
        v___x_2105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2105_, 0, v___x_2104_);
        return v___x_2105_;
    } else {
        let mut v_inheritedTraceOptions_2106_: *mut leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: u8 = 0;
        let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_2106_ = leanh::lean_ctor_get(v___y_2099_, 13);
        v___x_2107_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
        v___x_2108_ = l_Lean_Name_append(v___x_2107_, v___x_2096_);
        v___x_2109_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_2106_,
            v_options_2102_,
            v___x_2108_,
        );
        leanh::lean_dec(v___x_2108_);
        v___x_2110_ = leanh::lean_box((v___x_2109_) as usize);
        v___x_2111_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2111_, 0, v___x_2110_);
        return v___x_2111_;
    }
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__0___boxed(
    mut v___x_2112_: *mut leanh::LeanObject,
    mut v___y_2113_: *mut leanh::LeanObject,
    mut v___y_2114_: *mut leanh::LeanObject,
    mut v___y_2115_: *mut leanh::LeanObject,
    mut v___y_2116_: *mut leanh::LeanObject,
    mut v___y_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2118_ = l_Lean_Meta_injectionCore___lam__0(
        v___x_2112_,
        v___y_2113_,
        v___y_2114_,
        v___y_2115_,
        v___y_2116_,
    );
    leanh::lean_dec(v___y_2116_);
    leanh::lean_dec_ref(v___y_2115_);
    leanh::lean_dec(v___y_2114_);
    leanh::lean_dec_ref(v___y_2113_);
    return v_res_2118_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(
    mut v_msgData_2119_: *mut leanh::LeanObject,
    mut v___y_2120_: *mut leanh::LeanObject,
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v___y_2122_: *mut leanh::LeanObject,
    mut v___y_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = lean_st_ref_get(v___y_2123_);
    v_env_2126_ = leanh::lean_ctor_get(v___x_2125_, 0);
    leanh::lean_inc_ref(v_env_2126_);
    leanh::lean_dec(v___x_2125_);
    v___x_2127_ = lean_st_ref_get(v___y_2121_);
    v_mctx_2128_ = leanh::lean_ctor_get(v___x_2127_, 0);
    leanh::lean_inc_ref(v_mctx_2128_);
    leanh::lean_dec(v___x_2127_);
    v_lctx_2129_ = leanh::lean_ctor_get(v___y_2120_, 2);
    v_options_2130_ = leanh::lean_ctor_get(v___y_2122_, 2);
    leanh::lean_inc_ref(v_options_2130_);
    leanh::lean_inc_ref(v_lctx_2129_);
    v___x_2131_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2131_, 0, v_env_2126_);
    leanh::lean_ctor_set(v___x_2131_, 1, v_mctx_2128_);
    leanh::lean_ctor_set(v___x_2131_, 2, v_lctx_2129_);
    leanh::lean_ctor_set(v___x_2131_, 3, v_options_2130_);
    v___x_2132_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
    leanh::lean_ctor_set(v___x_2132_, 1, v_msgData_2119_);
    v___x_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    return v___x_2133_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2___boxed(
    mut v_msgData_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msgData_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
    leanh::lean_dec(v___y_2138_);
    leanh::lean_dec_ref(v___y_2137_);
    leanh::lean_dec(v___y_2136_);
    leanh::lean_dec_ref(v___y_2135_);
    return v_res_2140_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__0() -> f64 {
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: f64 = 0.0;
    v___x_2141_ = leanh::lean_unsigned_to_nat(0);
    v___x_2142_ = lean_float_of_nat(v___x_2141_);
    return v___x_2142_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
    mut v_cls_2146_: *mut leanh::LeanObject,
    mut v_msg_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2158_: u8 = 0;
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v_tid_2172_: u64 = 0;
    let mut v_traces_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: f64 = 0.0;
    let mut v___x_2179_: u8 = 0;
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v_isSharedCheck_2199_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2153_ = leanh::lean_ctor_get(v___y_2150_, 5);
                v___x_2154_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1_spec__2(v_msg_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
                v_a_2155_ = leanh::lean_ctor_get(v___x_2154_, 0);
                v_isSharedCheck_2199_ = (!leanh::lean_is_exclusive(v___x_2154_)) as u8;
                if v_isSharedCheck_2199_ == 0 {
                    v___x_2157_ = v___x_2154_;
                    v_isShared_2158_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2155_);
                    leanh::lean_dec(v___x_2154_);
                    v___x_2157_ = leanh::lean_box(0);
                    v_isShared_2158_ = v_isSharedCheck_2199_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2159_ = lean_st_ref_take(v___y_2151_);
                v_traceState_2160_ = leanh::lean_ctor_get(v___x_2159_, 4);
                v_env_2161_ = leanh::lean_ctor_get(v___x_2159_, 0);
                v_nextMacroScope_2162_ = leanh::lean_ctor_get(v___x_2159_, 1);
                v_ngen_2163_ = leanh::lean_ctor_get(v___x_2159_, 2);
                v_auxDeclNGen_2164_ = leanh::lean_ctor_get(v___x_2159_, 3);
                v_cache_2165_ = leanh::lean_ctor_get(v___x_2159_, 5);
                v_messages_2166_ = leanh::lean_ctor_get(v___x_2159_, 6);
                v_infoState_2167_ = leanh::lean_ctor_get(v___x_2159_, 7);
                v_snapshotTasks_2168_ = leanh::lean_ctor_get(v___x_2159_, 8);
                v_isSharedCheck_2198_ = (!leanh::lean_is_exclusive(v___x_2159_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2170_ = v___x_2159_;
                    v_isShared_2171_ = v_isSharedCheck_2198_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2168_);
                    leanh::lean_inc(v_infoState_2167_);
                    leanh::lean_inc(v_messages_2166_);
                    leanh::lean_inc(v_cache_2165_);
                    leanh::lean_inc(v_traceState_2160_);
                    leanh::lean_inc(v_auxDeclNGen_2164_);
                    leanh::lean_inc(v_ngen_2163_);
                    leanh::lean_inc(v_nextMacroScope_2162_);
                    leanh::lean_inc(v_env_2161_);
                    leanh::lean_dec(v___x_2159_);
                    v___x_2170_ = leanh::lean_box(0);
                    v_isShared_2171_ = v_isSharedCheck_2198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2172_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2160_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2173_ = leanh::lean_ctor_get(v_traceState_2160_, 0);
                v_isSharedCheck_2197_ =
                    (!leanh::lean_is_exclusive(v_traceState_2160_)) as u8;
                if v_isSharedCheck_2197_ == 0 {
                    v___x_2175_ = v_traceState_2160_;
                    v_isShared_2176_ = v_isSharedCheck_2197_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2173_);
                    leanh::lean_dec(v_traceState_2160_);
                    v___x_2175_ = leanh::lean_box(0);
                    v_isShared_2176_ = v_isSharedCheck_2197_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2177_ = leanh::lean_box(0);
                v___x_2178_ = leanh::lean_float_once(
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
                v___x_2181_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_2181_, 0, v_cls_2146_);
                leanh::lean_ctor_set(v___x_2181_, 1, v___x_2177_);
                leanh::lean_ctor_set(v___x_2181_, 2, v___x_2180_);
                leanh::lean_ctor_set_float(
                    v___x_2181_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2178_,
                );
                leanh::lean_ctor_set_float(
                    v___x_2181_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2178_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2181_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2179_,
                );
                v___x_2182_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1___closed__2;
                v___x_2183_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2183_, 0, v___x_2181_);
                leanh::lean_ctor_set(v___x_2183_, 1, v_a_2155_);
                leanh::lean_ctor_set(v___x_2183_, 2, v___x_2182_);
                leanh::lean_inc(v_ref_2153_);
                v___x_2184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2184_, 0, v_ref_2153_);
                leanh::lean_ctor_set(v___x_2184_, 1, v___x_2183_);
                v___x_2185_ = l_Lean_PersistentArray_push___redArg(v_traces_2173_, v___x_2184_);
                if v_isShared_2176_ == 0 {
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2185_);
                    v___x_2187_ = v___x_2175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2185_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2196_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2172_,
                    );
                    v___x_2187_ = v_reuseFailAlloc_2196_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2171_ == 0 {
                    leanh::lean_ctor_set(v___x_2170_, 4, v___x_2187_);
                    v___x_2189_ = v___x_2170_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_env_2161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_nextMacroScope_2162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_ngen_2163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_auxDeclNGen_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 4, v___x_2187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 5, v_cache_2165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 6, v_messages_2166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 7, v_infoState_2167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 8, v_snapshotTasks_2168_);
                    v___x_2189_ = v_reuseFailAlloc_2195_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2190_ = lean_st_ref_set(v___y_2151_, v___x_2189_);
                v___x_2191_ = leanh::lean_box(0);
                if v_isShared_2158_ == 0 {
                    leanh::lean_ctor_set(v___x_2157_, 0, v___x_2191_);
                    v___x_2193_ = v___x_2157_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
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
    mut v_cls_2200_: *mut leanh::LeanObject,
    mut v_msg_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
    mut v___y_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
    mut v___y_2205_: *mut leanh::LeanObject,
    mut v___y_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2207_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
        v_cls_2200_,
        v_msg_2201_,
        v___y_2202_,
        v___y_2203_,
        v___y_2204_,
        v___y_2205_,
    );
    leanh::lean_dec(v___y_2205_);
    leanh::lean_dec_ref(v___y_2204_);
    leanh::lean_dec(v___y_2203_);
    leanh::lean_dec_ref(v___y_2202_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_x_2208_: *mut leanh::LeanObject,
    mut v_x_2209_: *mut leanh::LeanObject,
    mut v_x_2210_: *mut leanh::LeanObject,
    mut v_x_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2212_ = leanh::lean_ctor_get(v_x_2208_, 0);
                v_vs_2213_ = leanh::lean_ctor_get(v_x_2208_, 1);
                v_isSharedCheck_2237_ = (!leanh::lean_is_exclusive(v_x_2208_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v___x_2215_ = v_x_2208_;
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2213_);
                    leanh::lean_inc(v_ks_2212_);
                    leanh::lean_dec(v_x_2208_);
                    v___x_2215_ = leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = lean_array_get_size(v_ks_2212_);
                v___x_2218_ = lean_nat_dec_lt(v_x_2209_, v___x_2217_);
                if v___x_2218_ == 0 {
                    leanh::lean_dec(v_x_2209_);
                    v___x_2219_ = lean_array_push(v_ks_2212_, v_x_2210_);
                    v___x_2220_ = lean_array_push(v_vs_2213_, v_x_2211_);
                    if v_isShared_2216_ == 0 {
                        leanh::lean_ctor_set(v___x_2215_, 1, v___x_2220_);
                        leanh::lean_ctor_set(v___x_2215_, 0, v___x_2219_);
                        v___x_2222_ = v___x_2215_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2220_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_ks_2212_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_vs_2213_);
                            v___x_2227_ = v_reuseFailAlloc_2231_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2232_ = lean_array_fset(v_ks_2212_, v_x_2209_, v_x_2210_);
                        v___x_2233_ = lean_array_fset(v_vs_2213_, v_x_2209_, v_x_2211_);
                        leanh::lean_dec(v_x_2209_);
                        if v_isShared_2216_ == 0 {
                            leanh::lean_ctor_set(v___x_2215_, 1, v___x_2233_);
                            leanh::lean_ctor_set(v___x_2215_, 0, v___x_2232_);
                            v___x_2235_ = v___x_2215_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2236_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
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
                v___x_2228_ = leanh::lean_unsigned_to_nat(1);
                v___x_2229_ = lean_nat_add(v_x_2209_, v___x_2228_);
                leanh::lean_dec(v_x_2209_);
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
    mut v_n_2238_: *mut leanh::LeanObject,
    mut v_k_2239_: *mut leanh::LeanObject,
    mut v_v_2240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_2247_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_2248_ = lean_usize_sub(v___x_2247_, v___x_2246_);
    return v___x_2248_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(
    mut v_x_2250_: *mut leanh::LeanObject,
    mut v_x_2251_: usize,
    mut v_x_2252_: usize,
    mut v_x_2253_: *mut leanh::LeanObject,
    mut v_x_2254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: usize = 0;
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v_j_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_v_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_node_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: u8 = 0;
    let mut v_ks_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2250_) == 0 {
                    v_es_2255_ = leanh::lean_ctor_get(v_x_2250_, 0);
                    v___x_2256_ = 5usize;
                    v___x_2257_ = 1usize;
                    v___x_2258_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2259_ = lean_usize_land(v_x_2251_, v___x_2258_);
                    v_j_2260_ = lean_usize_to_nat(v___x_2259_);
                    v___x_2261_ = lean_array_get_size(v_es_2255_);
                    v___x_2262_ = lean_nat_dec_lt(v_j_2260_, v___x_2261_);
                    if v___x_2262_ == 0 {
                        leanh::lean_dec(v_j_2260_);
                        leanh::lean_dec(v_x_2254_);
                        leanh::lean_dec(v_x_2253_);
                        return v_x_2250_;
                    } else {
                        leanh::lean_inc_ref(v_es_2255_);
                        v_isSharedCheck_2299_ = (!leanh::lean_is_exclusive(v_x_2250_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = leanh::lean_ctor_get(v_x_2250_, 0);
                            leanh::lean_dec(v_unused_2300_);
                            v___x_2264_ = v_x_2250_;
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2250_);
                            v___x_2264_ = leanh::lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2301_ = leanh::lean_ctor_get(v_x_2250_, 0);
                    v_vs_2302_ = leanh::lean_ctor_get(v_x_2250_, 1);
                    v_isSharedCheck_2322_ = (!leanh::lean_is_exclusive(v_x_2250_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2304_ = v_x_2250_;
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2302_);
                        leanh::lean_inc(v_ks_2301_);
                        leanh::lean_dec(v_x_2250_);
                        v___x_2304_ = leanh::lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2266_ = lean_array_fget(v_es_2255_, v_j_2260_);
                v___x_2267_ = leanh::lean_box(0);
                v_xs_x27_2268_ = lean_array_fset(v_es_2255_, v_j_2260_, v___x_2267_);
                match leanh::lean_obj_tag(v_v_2266_) {
                    0 => {
                        v_key_2275_ = leanh::lean_ctor_get(v_v_2266_, 0);
                        v_val_2276_ = leanh::lean_ctor_get(v_v_2266_, 1);
                        v_isSharedCheck_2286_ = (!leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2286_ == 0 {
                            v___x_2278_ = v_v_2266_;
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2276_);
                            leanh::lean_inc(v_key_2275_);
                            leanh::lean_dec(v_v_2266_);
                            v___x_2278_ = leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2287_ = leanh::lean_ctor_get(v_v_2266_, 0);
                        v_isSharedCheck_2297_ = (!leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2289_ = v_v_2266_;
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2287_);
                            leanh::lean_dec(v_v_2266_);
                            v___x_2289_ = leanh::lean_box(0);
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2298_, 0, v_x_2253_);
                        leanh::lean_ctor_set(v___x_2298_, 1, v_x_2254_);
                        v___y_2270_ = v___x_2298_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2271_ = lean_array_fset(v_xs_x27_2268_, v_j_2260_, v___y_2270_);
                leanh::lean_dec(v_j_2260_);
                if v_isShared_2265_ == 0 {
                    leanh::lean_ctor_set(v___x_2264_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
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
                    leanh::lean_del_object(v___x_2278_);
                    v___x_2281_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2275_,
                        v_val_2276_,
                        v_x_2253_,
                        v_x_2254_,
                    );
                    v___x_2282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
                    v___y_2270_ = v___x_2282_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2276_);
                    leanh::lean_dec(v_key_2275_);
                    if v_isShared_2279_ == 0 {
                        leanh::lean_ctor_set(v___x_2278_, 1, v_x_2254_);
                        leanh::lean_ctor_set(v___x_2278_, 0, v_x_2253_);
                        v___x_2284_ = v___x_2278_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_x_2253_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_x_2254_);
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
                    leanh::lean_ctor_set(v___x_2289_, 0, v___x_2293_);
                    v___x_2295_ = v___x_2289_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
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
                    v_reuseFailAlloc_2321_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_ks_2301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_vs_2302_);
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
                    v___x_2319_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
                    leanh::lean_dec(v___x_2318_);
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
                    v_ks_2311_ = leanh::lean_ctor_get(v_newNode_2308_, 0);
                    leanh::lean_inc_ref(v_ks_2311_);
                    v_vs_2312_ = leanh::lean_ctor_get(v_newNode_2308_, 1);
                    leanh::lean_inc_ref(v_vs_2312_);
                    leanh::lean_dec_ref(v_newNode_2308_);
                    v___x_2313_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2252_, v_ks_2311_, v_vs_2312_, v___x_2313_, v___x_2314_);
                    leanh::lean_dec_ref(v_vs_2312_);
                    leanh::lean_dec_ref(v_ks_2311_);
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
    mut v_keys_2324_: *mut leanh::LeanObject,
    mut v_vals_2325_: *mut leanh::LeanObject,
    mut v_i_2326_: *mut leanh::LeanObject,
    mut v_entries_2327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v_k_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_h_2333_: usize = 0;
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v_h_2339_: usize = 0;
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2328_ = lean_array_get_size(v_keys_2324_);
                v___x_2329_ = lean_nat_dec_lt(v_i_2326_, v___x_2328_);
                if v___x_2329_ == 0 {
                    leanh::lean_dec(v_i_2326_);
                    return v_entries_2327_;
                } else {
                    v_k_2330_ = lean_array_fget_borrowed(v_keys_2324_, v_i_2326_);
                    v_v_2331_ = lean_array_fget_borrowed(v_vals_2325_, v_i_2326_);
                    v___x_2332_ = l_Lean_instHashableMVarId_hash(v_k_2330_);
                    v_h_2333_ = lean_uint64_to_usize(v___x_2332_);
                    v___x_2334_ = 5usize;
                    v___x_2335_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2336_ = 1usize;
                    v___x_2337_ = lean_usize_sub(v_depth_2323_, v___x_2336_);
                    v___x_2338_ = lean_usize_mul(v___x_2334_, v___x_2337_);
                    v_h_2339_ = lean_usize_shift_right(v_h_2333_, v___x_2338_);
                    v___x_2340_ = lean_nat_add(v_i_2326_, v___x_2335_);
                    leanh::lean_dec(v_i_2326_);
                    leanh::lean_inc(v_v_2331_);
                    leanh::lean_inc(v_k_2330_);
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
    mut v_depth_2343_: *mut leanh::LeanObject,
    mut v_keys_2344_: *mut leanh::LeanObject,
    mut v_vals_2345_: *mut leanh::LeanObject,
    mut v_i_2346_: *mut leanh::LeanObject,
    mut v_entries_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2348_: usize = 0;
    let mut v_res_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2348_ = leanh::lean_unbox_usize(v_depth_2343_);
    leanh::lean_dec(v_depth_2343_);
    v_res_2349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_2348_, v_keys_2344_, v_vals_2345_, v_i_2346_, v_entries_2347_);
    leanh::lean_dec_ref(v_vals_2345_);
    leanh::lean_dec_ref(v_keys_2344_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_2350_: *mut leanh::LeanObject,
    mut v_x_2351_: *mut leanh::LeanObject,
    mut v_x_2352_: *mut leanh::LeanObject,
    mut v_x_2353_: *mut leanh::LeanObject,
    mut v_x_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_16678__boxed_2355_: usize = 0;
    let mut v_x_16679__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_16678__boxed_2355_ = leanh::lean_unbox_usize(v_x_2351_);
    leanh::lean_dec(v_x_2351_);
    v_x_16679__boxed_2356_ = leanh::lean_unbox_usize(v_x_2352_);
    leanh::lean_dec(v_x_2352_);
    v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2350_, v_x_16678__boxed_2355_, v_x_16679__boxed_2356_, v_x_2353_, v_x_2354_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(
    mut v_x_2358_: *mut leanh::LeanObject,
    mut v_x_2359_: *mut leanh::LeanObject,
    mut v_x_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2361_: u64 = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ = l_Lean_instHashableMVarId_hash(v_x_2359_);
    v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
    v___x_2363_ = 1usize;
    v___x_2364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2358_, v___x_2362_, v___x_2363_, v_x_2359_, v_x_2360_);
    return v___x_2364_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
    mut v_mvarId_2365_: *mut leanh::LeanObject,
    mut v_val_2366_: *mut leanh::LeanObject,
    mut v___y_2367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v_depth_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2369_ = lean_st_ref_take(v___y_2367_);
                v_mctx_2370_ = leanh::lean_ctor_get(v___x_2369_, 0);
                v_cache_2371_ = leanh::lean_ctor_get(v___x_2369_, 1);
                v_zetaDeltaFVarIds_2372_ = leanh::lean_ctor_get(v___x_2369_, 2);
                v_postponed_2373_ = leanh::lean_ctor_get(v___x_2369_, 3);
                v_diag_2374_ = leanh::lean_ctor_get(v___x_2369_, 4);
                v_isSharedCheck_2402_ = (!leanh::lean_is_exclusive(v___x_2369_)) as u8;
                if v_isSharedCheck_2402_ == 0 {
                    v___x_2376_ = v___x_2369_;
                    v_isShared_2377_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2374_);
                    leanh::lean_inc(v_postponed_2373_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2372_);
                    leanh::lean_inc(v_cache_2371_);
                    leanh::lean_inc(v_mctx_2370_);
                    leanh::lean_dec(v___x_2369_);
                    v___x_2376_ = leanh::lean_box(0);
                    v_isShared_2377_ = v_isSharedCheck_2402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2378_ = leanh::lean_ctor_get(v_mctx_2370_, 0);
                v_levelAssignDepth_2379_ = leanh::lean_ctor_get(v_mctx_2370_, 1);
                v_lmvarCounter_2380_ = leanh::lean_ctor_get(v_mctx_2370_, 2);
                v_mvarCounter_2381_ = leanh::lean_ctor_get(v_mctx_2370_, 3);
                v_lDecls_2382_ = leanh::lean_ctor_get(v_mctx_2370_, 4);
                v_decls_2383_ = leanh::lean_ctor_get(v_mctx_2370_, 5);
                v_userNames_2384_ = leanh::lean_ctor_get(v_mctx_2370_, 6);
                v_lAssignment_2385_ = leanh::lean_ctor_get(v_mctx_2370_, 7);
                v_eAssignment_2386_ = leanh::lean_ctor_get(v_mctx_2370_, 8);
                v_dAssignment_2387_ = leanh::lean_ctor_get(v_mctx_2370_, 9);
                v_isSharedCheck_2401_ = (!leanh::lean_is_exclusive(v_mctx_2370_)) as u8;
                if v_isSharedCheck_2401_ == 0 {
                    v___x_2389_ = v_mctx_2370_;
                    v_isShared_2390_ = v_isSharedCheck_2401_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_2387_);
                    leanh::lean_inc(v_eAssignment_2386_);
                    leanh::lean_inc(v_lAssignment_2385_);
                    leanh::lean_inc(v_userNames_2384_);
                    leanh::lean_inc(v_decls_2383_);
                    leanh::lean_inc(v_lDecls_2382_);
                    leanh::lean_inc(v_mvarCounter_2381_);
                    leanh::lean_inc(v_lmvarCounter_2380_);
                    leanh::lean_inc(v_levelAssignDepth_2379_);
                    leanh::lean_inc(v_depth_2378_);
                    leanh::lean_dec(v_mctx_2370_);
                    v___x_2389_ = leanh::lean_box(0);
                    v_isShared_2390_ = v_isSharedCheck_2401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2391_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_eAssignment_2386_, v_mvarId_2365_, v_val_2366_);
                if v_isShared_2390_ == 0 {
                    leanh::lean_ctor_set(v___x_2389_, 8, v___x_2391_);
                    v___x_2393_ = v___x_2389_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_depth_2378_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2400_,
                        1,
                        v_levelAssignDepth_2379_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_lmvarCounter_2380_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_mvarCounter_2381_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_lDecls_2382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 5, v_decls_2383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_userNames_2384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_lAssignment_2385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 8, v___x_2391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 9, v_dAssignment_2387_);
                    v___x_2393_ = v_reuseFailAlloc_2400_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2377_ == 0 {
                    leanh::lean_ctor_set(v___x_2376_, 0, v___x_2393_);
                    v___x_2395_ = v___x_2376_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_cache_2371_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2399_,
                        2,
                        v_zetaDeltaFVarIds_2372_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_postponed_2373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_diag_2374_);
                    v___x_2395_ = v_reuseFailAlloc_2399_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2396_ = lean_st_ref_set(v___y_2367_, v___x_2395_);
                v___x_2397_ = leanh::lean_box(0);
                v___x_2398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2398_, 0, v___x_2397_);
                return v___x_2398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg___boxed(
    mut v_mvarId_2403_: *mut leanh::LeanObject,
    mut v_val_2404_: *mut leanh::LeanObject,
    mut v___y_2405_: *mut leanh::LeanObject,
    mut v___y_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
        v_mvarId_2403_,
        v_val_2404_,
        v___y_2405_,
    );
    leanh::lean_dec(v___y_2405_);
    return v_res_2407_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_Meta_injectionCore___lam__1___closed__1;
    v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__2_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__2,
    );
    v___x_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_Meta_injectionCore___lam__1___closed__5;
    v___x_2419_ = l_Lean_MessageData_ofFormat(v___x_2418_);
    return v___x_2419_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__6_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__6,
    );
    v___x_2421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2421_, 0, v___x_2420_);
    return v___x_2421_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = l_Lean_Meta_injectionCore___lam__1___closed__8;
    v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
    return v___x_2424_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = l_Lean_Meta_injectionCore___lam__1___closed__10;
    v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
    return v___x_2427_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
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
-> *mut leanh::LeanObject {
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Lean_Meta_injectionCore___lam__1___closed__15;
    v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_Meta_injectionCore___lam__1___closed__17;
    v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
    return v___x_2438_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = l_Lean_Meta_injectionCore___lam__1___closed__22;
    v___x_2446_ = l_Lean_MessageData_ofFormat(v___x_2445_);
    return v___x_2446_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__23_once),
        _init_l_Lean_Meta_injectionCore___lam__1___closed__23,
    );
    v___x_2448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2448_, 0, v___x_2447_);
    return v___x_2448_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = l_Lean_Meta_injectionCore___lam__1___closed__27;
    v___x_2453_ = l_Lean_stringToMessageData(v___x_2452_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_Meta_injectionCore___lam__1___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = l_Lean_Meta_injectionCore___lam__1___closed__29;
    v___x_2456_ = l_Lean_stringToMessageData(v___x_2455_);
    return v___x_2456_;
}
pub unsafe fn l_Lean_Meta_injectionCore___lam__1(
    mut v_mvarId_2460_: *mut leanh::LeanObject,
    mut v___x_2461_: *mut leanh::LeanObject,
    mut v_fvarId_2462_: *mut leanh::LeanObject,
    mut v___x_2463_: *mut leanh::LeanObject,
    mut v___y_2464_: *mut leanh::LeanObject,
    mut v___y_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
    mut v___y_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut v_unused_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2536_: u8 = 0;
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_reuseFailAlloc_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_a_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut v_unused_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2582_: u8 = 0;
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2586_: u8 = 0;
    let mut v_a_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2590_: u8 = 0;
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2594_: u8 = 0;
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_a_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut v___y_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v_trackZetaDelta_2667_: u8 = 0;
    let mut v_zetaDeltaSet_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2674_: u8 = 0;
    let mut v_inTypeClassResolution_2675_: u8 = 0;
    let mut v_cacheInferType_2676_: u8 = 0;
    let mut v___x_2677_: u8 = 0;
    let mut v_config_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: u64 = 0;
    let mut v___x_2681_: u64 = 0;
    let mut v___x_2682_: u64 = 0;
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    let mut v_key_2685_: u64 = 0;
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2710_: u8 = 0;
    let mut v_a_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2718_: u8 = 0;
    let mut v_a_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut v_a_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_type_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prf_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_reuseFailAlloc_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_a_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2814_: u8 = 0;
    let mut v_a_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2850_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2854_: u8 = 0;
    let mut v_a_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2862_: u8 = 0;
    let mut v_a_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_a_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_2461_);
                leanh::lean_inc(v_mvarId_2460_);
                v___x_2823_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_2460_,
                    v___x_2461_,
                    v___y_2464_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                );
                if leanh::lean_obj_tag(v___x_2823_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2823_, 1);
                    leanh::lean_inc(v_fvarId_2462_);
                    v___x_2824_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_2462_,
                        v___y_2464_,
                        v___y_2466_,
                        v___y_2467_,
                    );
                    if leanh::lean_obj_tag(v___x_2824_) == 0 {
                        v_a_2825_ = leanh::lean_ctor_get(v___x_2824_, 0);
                        leanh::lean_inc(v_a_2825_);
                        leanh::lean_dec_ref_known(v___x_2824_, 1);
                        v___x_2826_ = l_Lean_LocalDecl_type(v_a_2825_);
                        leanh::lean_dec(v_a_2825_);
                        leanh::lean_inc(v___y_2467_);
                        leanh::lean_inc_ref(v___y_2466_);
                        leanh::lean_inc(v___y_2465_);
                        leanh::lean_inc_ref(v___y_2464_);
                        v___x_2827_ = lean_whnf(
                            v___x_2826_,
                            v___y_2464_,
                            v___y_2465_,
                            v___y_2466_,
                            v___y_2467_,
                        );
                        if leanh::lean_obj_tag(v___x_2827_) == 0 {
                            v_a_2828_ = leanh::lean_ctor_get(v___x_2827_, 0);
                            leanh::lean_inc(v_a_2828_);
                            leanh::lean_dec_ref_known(v___x_2827_, 1);
                            leanh::lean_inc(v_fvarId_2462_);
                            v___x_2829_ = l_Lean_mkFVar(v_fvarId_2462_);
                            v___x_2830_ = l_Lean_Meta_injectionCore___lam__1___closed__32;
                            v___x_2831_ = leanh::lean_unsigned_to_nat(4);
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
                                leanh::lean_dec_ref(v___x_2835_);
                                v___x_2837_ = l_Lean_Expr_appArg_x21(v___x_2833_);
                                leanh::lean_dec_ref(v___x_2833_);
                                v___x_2838_ = l_Lean_Meta_isExprDefEq(
                                    v___x_2836_,
                                    v___x_2837_,
                                    v___y_2464_,
                                    v___y_2465_,
                                    v___y_2466_,
                                    v___y_2467_,
                                );
                                if leanh::lean_obj_tag(v___x_2838_) == 0 {
                                    v_a_2839_ = leanh::lean_ctor_get(v___x_2838_, 0);
                                    leanh::lean_inc(v_a_2839_);
                                    leanh::lean_dec_ref_known(v___x_2838_, 1);
                                    v___x_2840_ = (leanh::lean_unbox(v_a_2839_) as u8);
                                    leanh::lean_dec(v_a_2839_);
                                    if v___x_2840_ == 0 {
                                        leanh::lean_dec_ref(v___x_2834_);
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
                                        leanh::lean_dec_ref(v___x_2834_);
                                        v___x_2842_ = l_Lean_Expr_appArg_x21(v_a_2828_);
                                        leanh::lean_dec(v_a_2828_);
                                        v___x_2843_ = l_Lean_Meta_mkEq(
                                            v___x_2841_,
                                            v___x_2842_,
                                            v___y_2464_,
                                            v___y_2465_,
                                            v___y_2466_,
                                            v___y_2467_,
                                        );
                                        if leanh::lean_obj_tag(v___x_2843_) == 0 {
                                            v_a_2844_ = leanh::lean_ctor_get(v___x_2843_, 0);
                                            leanh::lean_inc(v_a_2844_);
                                            leanh::lean_dec_ref_known(v___x_2843_, 1);
                                            v___x_2845_ = l_Lean_Meta_mkEqOfHEq(
                                                v___x_2829_,
                                                v___x_2832_,
                                                v___y_2464_,
                                                v___y_2465_,
                                                v___y_2466_,
                                                v___y_2467_,
                                            );
                                            if leanh::lean_obj_tag(v___x_2845_) == 0 {
                                                v_a_2846_ =
                                                    leanh::lean_ctor_get(v___x_2845_, 0);
                                                leanh::lean_inc(v_a_2846_);
                                                leanh::lean_dec_ref_known(v___x_2845_, 1);
                                                v_type_2738_ = v_a_2844_;
                                                v_prf_2739_ = v_a_2846_;
                                                v___y_2740_ = v___y_2464_;
                                                v___y_2741_ = v___y_2465_;
                                                v___y_2742_ = v___y_2466_;
                                                v___y_2743_ = v___y_2467_;
                                                state = 38;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_a_2844_);
                                                leanh::lean_dec(v___y_2467_);
                                                leanh::lean_dec_ref(v___y_2466_);
                                                leanh::lean_dec(v___y_2465_);
                                                leanh::lean_dec_ref(v___y_2464_);
                                                leanh::lean_dec_ref(v___x_2463_);
                                                leanh::lean_dec(v_fvarId_2462_);
                                                leanh::lean_dec(v___x_2461_);
                                                leanh::lean_dec(v_mvarId_2460_);
                                                v_a_2847_ =
                                                    leanh::lean_ctor_get(v___x_2845_, 0);
                                                v_isSharedCheck_2854_ =
                                                    (!leanh::lean_is_exclusive(v___x_2845_))
                                                        as u8;
                                                if v_isSharedCheck_2854_ == 0 {
                                                    v___x_2849_ = v___x_2845_;
                                                    v_isShared_2850_ = v_isSharedCheck_2854_;
                                                    state = 51;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2847_);
                                                    leanh::lean_dec(v___x_2845_);
                                                    v___x_2849_ = leanh::lean_box(0);
                                                    v_isShared_2850_ = v_isSharedCheck_2854_;
                                                    state = 51;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_2829_);
                                            leanh::lean_dec(v___y_2467_);
                                            leanh::lean_dec_ref(v___y_2466_);
                                            leanh::lean_dec(v___y_2465_);
                                            leanh::lean_dec_ref(v___y_2464_);
                                            leanh::lean_dec_ref(v___x_2463_);
                                            leanh::lean_dec(v_fvarId_2462_);
                                            leanh::lean_dec(v___x_2461_);
                                            leanh::lean_dec(v_mvarId_2460_);
                                            v_a_2855_ = leanh::lean_ctor_get(v___x_2843_, 0);
                                            v_isSharedCheck_2862_ =
                                                (!leanh::lean_is_exclusive(v___x_2843_))
                                                    as u8;
                                            if v_isSharedCheck_2862_ == 0 {
                                                v___x_2857_ = v___x_2843_;
                                                v_isShared_2858_ = v_isSharedCheck_2862_;
                                                state = 53;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2855_);
                                                leanh::lean_dec(v___x_2843_);
                                                v___x_2857_ = leanh::lean_box(0);
                                                v_isShared_2858_ = v_isSharedCheck_2862_;
                                                state = 53;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2834_);
                                    leanh::lean_dec_ref(v___x_2829_);
                                    leanh::lean_dec(v_a_2828_);
                                    leanh::lean_dec(v___y_2467_);
                                    leanh::lean_dec_ref(v___y_2466_);
                                    leanh::lean_dec(v___y_2465_);
                                    leanh::lean_dec_ref(v___y_2464_);
                                    leanh::lean_dec_ref(v___x_2463_);
                                    leanh::lean_dec(v_fvarId_2462_);
                                    leanh::lean_dec(v___x_2461_);
                                    leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2863_ = leanh::lean_ctor_get(v___x_2838_, 0);
                                    v_isSharedCheck_2870_ =
                                        (!leanh::lean_is_exclusive(v___x_2838_)) as u8;
                                    if v_isSharedCheck_2870_ == 0 {
                                        v___x_2865_ = v___x_2838_;
                                        v_isShared_2866_ = v_isSharedCheck_2870_;
                                        state = 55;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2863_);
                                        leanh::lean_dec(v___x_2838_);
                                        v___x_2865_ = leanh::lean_box(0);
                                        v_isShared_2866_ = v_isSharedCheck_2870_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v___y_2467_);
                            leanh::lean_dec_ref(v___y_2466_);
                            leanh::lean_dec(v___y_2465_);
                            leanh::lean_dec_ref(v___y_2464_);
                            leanh::lean_dec_ref(v___x_2463_);
                            leanh::lean_dec(v_fvarId_2462_);
                            leanh::lean_dec(v___x_2461_);
                            leanh::lean_dec(v_mvarId_2460_);
                            v_a_2871_ = leanh::lean_ctor_get(v___x_2827_, 0);
                            v_isSharedCheck_2878_ =
                                (!leanh::lean_is_exclusive(v___x_2827_)) as u8;
                            if v_isSharedCheck_2878_ == 0 {
                                v___x_2873_ = v___x_2827_;
                                v_isShared_2874_ = v_isSharedCheck_2878_;
                                state = 57;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2871_);
                                leanh::lean_dec(v___x_2827_);
                                v___x_2873_ = leanh::lean_box(0);
                                v_isShared_2874_ = v_isSharedCheck_2878_;
                                state = 57;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_2467_);
                        leanh::lean_dec_ref(v___y_2466_);
                        leanh::lean_dec(v___y_2465_);
                        leanh::lean_dec_ref(v___y_2464_);
                        leanh::lean_dec_ref(v___x_2463_);
                        leanh::lean_dec(v_fvarId_2462_);
                        leanh::lean_dec(v___x_2461_);
                        leanh::lean_dec(v_mvarId_2460_);
                        v_a_2879_ = leanh::lean_ctor_get(v___x_2824_, 0);
                        v_isSharedCheck_2886_ =
                            (!leanh::lean_is_exclusive(v___x_2824_)) as u8;
                        if v_isSharedCheck_2886_ == 0 {
                            v___x_2881_ = v___x_2824_;
                            v_isShared_2882_ = v_isSharedCheck_2886_;
                            state = 59;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2879_);
                            leanh::lean_dec(v___x_2824_);
                            v___x_2881_ = leanh::lean_box(0);
                            v_isShared_2882_ = v_isSharedCheck_2886_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2467_);
                    leanh::lean_dec_ref(v___y_2466_);
                    leanh::lean_dec(v___y_2465_);
                    leanh::lean_dec_ref(v___y_2464_);
                    leanh::lean_dec_ref(v___x_2463_);
                    leanh::lean_dec(v_fvarId_2462_);
                    leanh::lean_dec(v___x_2461_);
                    leanh::lean_dec(v_mvarId_2460_);
                    v_a_2887_ = leanh::lean_ctor_get(v___x_2823_, 0);
                    v_isSharedCheck_2894_ = (!leanh::lean_is_exclusive(v___x_2823_)) as u8;
                    if v_isSharedCheck_2894_ == 0 {
                        v___x_2889_ = v___x_2823_;
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 61;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2887_);
                        leanh::lean_dec(v___x_2823_);
                        v___x_2889_ = leanh::lean_box(0);
                        v_isShared_2890_ = v_isSharedCheck_2894_;
                        state = 61;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2474_ = leanh::lean_obj_once(
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
                leanh::lean_dec(v___y_2473_);
                leanh::lean_dec_ref(v___y_2472_);
                leanh::lean_dec(v___y_2471_);
                leanh::lean_dec_ref(v___y_2470_);
                return v___x_2475_;
            }
            2 => {
                v___x_2481_ = leanh::lean_obj_once(
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
                leanh::lean_dec(v___y_2480_);
                leanh::lean_dec_ref(v___y_2479_);
                leanh::lean_dec(v___y_2478_);
                leanh::lean_dec_ref(v___y_2477_);
                return v___x_2482_;
            }
            3 => {
                v___x_2486_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2486_, 0, v___y_2485_);
                leanh::lean_ctor_set(v___x_2486_, 1, v___y_2484_);
                v___x_2487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2487_, 0, v___x_2486_);
                return v___x_2487_;
            }
            4 => {
                v_toConstantVal_2498_ = leanh::lean_ctor_get(v___y_2493_, 0);
                v_toConstantVal_2499_ = leanh::lean_ctor_get(v___y_2492_, 0);
                leanh::lean_inc_ref(v_toConstantVal_2499_);
                leanh::lean_dec_ref(v___y_2492_);
                v_numFields_2500_ = leanh::lean_ctor_get(v___y_2493_, 4);
                leanh::lean_inc(v_numFields_2500_);
                v_name_2501_ = leanh::lean_ctor_get(v_toConstantVal_2498_, 0);
                v_name_2502_ = leanh::lean_ctor_get(v_toConstantVal_2499_, 0);
                leanh::lean_inc(v_name_2502_);
                leanh::lean_dec_ref(v_toConstantVal_2499_);
                v___x_2503_ = lean_name_eq(v_name_2501_, v_name_2502_);
                leanh::lean_dec(v_name_2502_);
                if v___x_2503_ == 0 {
                    leanh::lean_dec(v_numFields_2500_);
                    leanh::lean_dec(v___y_2497_);
                    leanh::lean_dec_ref(v___y_2496_);
                    leanh::lean_dec_ref(v___y_2494_);
                    leanh::lean_dec_ref(v___y_2493_);
                    leanh::lean_dec(v___y_2491_);
                    leanh::lean_dec_ref(v___y_2490_);
                    leanh::lean_dec(v_fvarId_2462_);
                    leanh::lean_dec(v___x_2461_);
                    v___x_2504_ =
                        l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
                            v_mvarId_2460_,
                            v___y_2489_,
                            v___y_2495_,
                        );
                    leanh::lean_dec(v___y_2495_);
                    v_isSharedCheck_2512_ = (!leanh::lean_is_exclusive(v___x_2504_)) as u8;
                    if v_isSharedCheck_2512_ == 0 {
                        v_unused_2513_ = leanh::lean_ctor_get(v___x_2504_, 0);
                        leanh::lean_dec(v_unused_2513_);
                        v___x_2506_ = v___x_2504_;
                        v_isShared_2507_ = v_isSharedCheck_2512_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2504_);
                        v___x_2506_ = leanh::lean_box(0);
                        v_isShared_2507_ = v_isSharedCheck_2512_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___y_2497_);
                    leanh::lean_inc_ref(v___y_2496_);
                    leanh::lean_inc(v___y_2495_);
                    leanh::lean_inc_ref(v___y_2494_);
                    leanh::lean_inc_ref(v___y_2489_);
                    v___x_2514_ = lean_infer_type(
                        v___y_2489_,
                        v___y_2494_,
                        v___y_2495_,
                        v___y_2496_,
                        v___y_2497_,
                    );
                    if leanh::lean_obj_tag(v___x_2514_) == 0 {
                        v_a_2515_ = leanh::lean_ctor_get(v___x_2514_, 0);
                        leanh::lean_inc(v_a_2515_);
                        leanh::lean_dec_ref_known(v___x_2514_, 1);
                        v___x_2516_ = l_Lean_Meta_whnfD(
                            v_a_2515_,
                            v___y_2494_,
                            v___y_2495_,
                            v___y_2496_,
                            v___y_2497_,
                        );
                        if leanh::lean_obj_tag(v___x_2516_) == 0 {
                            v_a_2517_ = leanh::lean_ctor_get(v___x_2516_, 0);
                            leanh::lean_inc(v_a_2517_);
                            leanh::lean_dec_ref_known(v___x_2516_, 1);
                            if leanh::lean_obj_tag(v_a_2517_) == 7 {
                                leanh::lean_dec_ref(v___y_2490_);
                                leanh::lean_dec(v___x_2461_);
                                v_binderType_2518_ = leanh::lean_ctor_get(v_a_2517_, 1);
                                leanh::lean_inc_ref(v_binderType_2518_);
                                leanh::lean_dec_ref_known(v_a_2517_, 3);
                                leanh::lean_inc(v_mvarId_2460_);
                                v___x_2519_ = l_Lean_MVarId_getTag(
                                    v_mvarId_2460_,
                                    v___y_2494_,
                                    v___y_2495_,
                                    v___y_2496_,
                                    v___y_2497_,
                                );
                                if leanh::lean_obj_tag(v___x_2519_) == 0 {
                                    v_a_2520_ = leanh::lean_ctor_get(v___x_2519_, 0);
                                    leanh::lean_inc(v_a_2520_);
                                    leanh::lean_dec_ref_known(v___x_2519_, 1);
                                    v___x_2521_ = l_Lean_Expr_headBeta(v_binderType_2518_);
                                    v___x_2522_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                        v___x_2521_,
                                        v_a_2520_,
                                        v___y_2494_,
                                        v___y_2495_,
                                        v___y_2496_,
                                        v___y_2497_,
                                    );
                                    if leanh::lean_obj_tag(v___x_2522_) == 0 {
                                        v_a_2523_ = leanh::lean_ctor_get(v___x_2522_, 0);
                                        leanh::lean_inc_n(v_a_2523_, 2);
                                        leanh::lean_dec_ref_known(v___x_2522_, 1);
                                        v___x_2524_ =
                                            l_Lean_Expr_app___override(v___y_2489_, v_a_2523_);
                                        v___x_2525_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(v_mvarId_2460_, v___x_2524_, v___y_2495_);
                                        v_isSharedCheck_2577_ =
                                            (!leanh::lean_is_exclusive(v___x_2525_)) as u8;
                                        if v_isSharedCheck_2577_ == 0 {
                                            v_unused_2578_ =
                                                leanh::lean_ctor_get(v___x_2525_, 0);
                                            leanh::lean_dec(v_unused_2578_);
                                            v___x_2527_ = v___x_2525_;
                                            v_isShared_2528_ = v_isSharedCheck_2577_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_2525_);
                                            v___x_2527_ = leanh::lean_box(0);
                                            v_isShared_2528_ = v_isSharedCheck_2577_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_numFields_2500_);
                                        leanh::lean_dec(v___y_2497_);
                                        leanh::lean_dec_ref(v___y_2496_);
                                        leanh::lean_dec(v___y_2495_);
                                        leanh::lean_dec_ref(v___y_2494_);
                                        leanh::lean_dec_ref(v___y_2493_);
                                        leanh::lean_dec(v___y_2491_);
                                        leanh::lean_dec_ref(v___y_2489_);
                                        leanh::lean_dec(v_fvarId_2462_);
                                        leanh::lean_dec(v_mvarId_2460_);
                                        v_a_2579_ = leanh::lean_ctor_get(v___x_2522_, 0);
                                        v_isSharedCheck_2586_ =
                                            (!leanh::lean_is_exclusive(v___x_2522_)) as u8;
                                        if v_isSharedCheck_2586_ == 0 {
                                            v___x_2581_ = v___x_2522_;
                                            v_isShared_2582_ = v_isSharedCheck_2586_;
                                            state = 15;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2579_);
                                            leanh::lean_dec(v___x_2522_);
                                            v___x_2581_ = leanh::lean_box(0);
                                            v_isShared_2582_ = v_isSharedCheck_2586_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_binderType_2518_);
                                    leanh::lean_dec(v_numFields_2500_);
                                    leanh::lean_dec(v___y_2497_);
                                    leanh::lean_dec_ref(v___y_2496_);
                                    leanh::lean_dec(v___y_2495_);
                                    leanh::lean_dec_ref(v___y_2494_);
                                    leanh::lean_dec_ref(v___y_2493_);
                                    leanh::lean_dec(v___y_2491_);
                                    leanh::lean_dec_ref(v___y_2489_);
                                    leanh::lean_dec(v_fvarId_2462_);
                                    leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2587_ = leanh::lean_ctor_get(v___x_2519_, 0);
                                    v_isSharedCheck_2594_ =
                                        (!leanh::lean_is_exclusive(v___x_2519_)) as u8;
                                    if v_isSharedCheck_2594_ == 0 {
                                        v___x_2589_ = v___x_2519_;
                                        v_isShared_2590_ = v_isSharedCheck_2594_;
                                        state = 17;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2587_);
                                        leanh::lean_dec(v___x_2519_);
                                        v___x_2589_ = leanh::lean_box(0);
                                        v_isShared_2590_ = v_isSharedCheck_2594_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_numFields_2500_);
                                leanh::lean_dec_ref(v___y_2493_);
                                leanh::lean_dec_ref(v___y_2489_);
                                leanh::lean_dec(v_fvarId_2462_);
                                leanh::lean_inc(v___y_2497_);
                                leanh::lean_inc_ref(v___y_2496_);
                                leanh::lean_inc(v___y_2495_);
                                leanh::lean_inc_ref(v___y_2494_);
                                v___x_2595_ = leanh::lean_apply_5(
                                    v___y_2490_,
                                    v___y_2494_,
                                    v___y_2495_,
                                    v___y_2496_,
                                    v___y_2497_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_2595_) == 0 {
                                    v_a_2596_ = leanh::lean_ctor_get(v___x_2595_, 0);
                                    leanh::lean_inc(v_a_2596_);
                                    leanh::lean_dec_ref_known(v___x_2595_, 1);
                                    v___x_2597_ = (leanh::lean_unbox(v_a_2596_) as u8);
                                    leanh::lean_dec(v_a_2596_);
                                    if v___x_2597_ == 0 {
                                        leanh::lean_dec(v_a_2517_);
                                        leanh::lean_dec(v___y_2491_);
                                        v___y_2470_ = v___y_2494_;
                                        v___y_2471_ = v___y_2495_;
                                        v___y_2472_ = v___y_2496_;
                                        v___y_2473_ = v___y_2497_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__13_once), _init_l_Lean_Meta_injectionCore___lam__1___closed__13);
                                        v___x_2599_ = l_Lean_indentExpr(v_a_2517_);
                                        v___x_2600_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                                        leanh::lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                                        v___x_2601_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(v___y_2491_, v___x_2600_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
                                        if leanh::lean_obj_tag(v___x_2601_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_2601_, 1);
                                            v___y_2470_ = v___y_2494_;
                                            v___y_2471_ = v___y_2495_;
                                            v___y_2472_ = v___y_2496_;
                                            v___y_2473_ = v___y_2497_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___y_2497_);
                                            leanh::lean_dec_ref(v___y_2496_);
                                            leanh::lean_dec(v___y_2495_);
                                            leanh::lean_dec_ref(v___y_2494_);
                                            leanh::lean_dec(v___x_2461_);
                                            leanh::lean_dec(v_mvarId_2460_);
                                            v_a_2602_ = leanh::lean_ctor_get(v___x_2601_, 0);
                                            v_isSharedCheck_2609_ =
                                                (!leanh::lean_is_exclusive(v___x_2601_))
                                                    as u8;
                                            if v_isSharedCheck_2609_ == 0 {
                                                v___x_2604_ = v___x_2601_;
                                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                                state = 19;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2602_);
                                                leanh::lean_dec(v___x_2601_);
                                                v___x_2604_ = leanh::lean_box(0);
                                                v_isShared_2605_ = v_isSharedCheck_2609_;
                                                state = 19;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_2517_);
                                    leanh::lean_dec(v___y_2497_);
                                    leanh::lean_dec_ref(v___y_2496_);
                                    leanh::lean_dec(v___y_2495_);
                                    leanh::lean_dec_ref(v___y_2494_);
                                    leanh::lean_dec(v___y_2491_);
                                    leanh::lean_dec(v___x_2461_);
                                    leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2610_ = leanh::lean_ctor_get(v___x_2595_, 0);
                                    v_isSharedCheck_2617_ =
                                        (!leanh::lean_is_exclusive(v___x_2595_)) as u8;
                                    if v_isSharedCheck_2617_ == 0 {
                                        v___x_2612_ = v___x_2595_;
                                        v_isShared_2613_ = v_isSharedCheck_2617_;
                                        state = 21;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2610_);
                                        leanh::lean_dec(v___x_2595_);
                                        v___x_2612_ = leanh::lean_box(0);
                                        v_isShared_2613_ = v_isSharedCheck_2617_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_numFields_2500_);
                            leanh::lean_dec(v___y_2497_);
                            leanh::lean_dec_ref(v___y_2496_);
                            leanh::lean_dec(v___y_2495_);
                            leanh::lean_dec_ref(v___y_2494_);
                            leanh::lean_dec_ref(v___y_2493_);
                            leanh::lean_dec(v___y_2491_);
                            leanh::lean_dec_ref(v___y_2490_);
                            leanh::lean_dec_ref(v___y_2489_);
                            leanh::lean_dec(v_fvarId_2462_);
                            leanh::lean_dec(v___x_2461_);
                            leanh::lean_dec(v_mvarId_2460_);
                            v_a_2618_ = leanh::lean_ctor_get(v___x_2516_, 0);
                            v_isSharedCheck_2625_ =
                                (!leanh::lean_is_exclusive(v___x_2516_)) as u8;
                            if v_isSharedCheck_2625_ == 0 {
                                v___x_2620_ = v___x_2516_;
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2618_);
                                leanh::lean_dec(v___x_2516_);
                                v___x_2620_ = leanh::lean_box(0);
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_numFields_2500_);
                        leanh::lean_dec(v___y_2497_);
                        leanh::lean_dec_ref(v___y_2496_);
                        leanh::lean_dec(v___y_2495_);
                        leanh::lean_dec_ref(v___y_2494_);
                        leanh::lean_dec_ref(v___y_2493_);
                        leanh::lean_dec(v___y_2491_);
                        leanh::lean_dec_ref(v___y_2490_);
                        leanh::lean_dec_ref(v___y_2489_);
                        leanh::lean_dec(v_fvarId_2462_);
                        leanh::lean_dec(v___x_2461_);
                        leanh::lean_dec(v_mvarId_2460_);
                        v_a_2626_ = leanh::lean_ctor_get(v___x_2514_, 0);
                        v_isSharedCheck_2633_ =
                            (!leanh::lean_is_exclusive(v___x_2514_)) as u8;
                        if v_isSharedCheck_2633_ == 0 {
                            v___x_2628_ = v___x_2514_;
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 25;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2626_);
                            leanh::lean_dec(v___x_2514_);
                            v___x_2628_ = leanh::lean_box(0);
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_2508_ = leanh::lean_box(0);
                if v_isShared_2507_ == 0 {
                    leanh::lean_ctor_set(v___x_2506_, 0, v___x_2508_);
                    v___x_2510_ = v___x_2506_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
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
                leanh::lean_dec(v_a_2523_);
                v___x_2530_ = l_Lean_MVarId_tryClear(
                    v___x_2529_,
                    v_fvarId_2462_,
                    v___y_2494_,
                    v___y_2495_,
                    v___y_2496_,
                    v___y_2497_,
                );
                if leanh::lean_obj_tag(v___x_2530_) == 0 {
                    v_a_2531_ = leanh::lean_ctor_get(v___x_2530_, 0);
                    leanh::lean_inc(v_a_2531_);
                    leanh::lean_dec_ref_known(v___x_2530_, 1);
                    v___x_2532_ = l_Lean_Meta_getCtorNumPropFields(
                        v___y_2493_,
                        v___y_2494_,
                        v___y_2495_,
                        v___y_2496_,
                        v___y_2497_,
                    );
                    if leanh::lean_obj_tag(v___x_2532_) == 0 {
                        v_options_2533_ = leanh::lean_ctor_get(v___y_2496_, 2);
                        v_a_2534_ = leanh::lean_ctor_get(v___x_2532_, 0);
                        leanh::lean_inc(v_a_2534_);
                        leanh::lean_dec_ref_known(v___x_2532_, 1);
                        v_inheritedTraceOptions_2535_ =
                            leanh::lean_ctor_get(v___y_2496_, 13);
                        v_hasTrace_2536_ = leanh::lean_ctor_get_uint8(
                            v_options_2533_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        v___x_2537_ = lean_nat_sub(v_numFields_2500_, v_a_2534_);
                        leanh::lean_dec(v_a_2534_);
                        leanh::lean_dec(v_numFields_2500_);
                        if v_hasTrace_2536_ == 0 {
                            leanh::lean_del_object(v___x_2527_);
                            leanh::lean_dec(v___y_2497_);
                            leanh::lean_dec_ref(v___y_2496_);
                            leanh::lean_dec(v___y_2495_);
                            leanh::lean_dec_ref(v___y_2494_);
                            leanh::lean_dec(v___y_2491_);
                            v___y_2484_ = v___x_2537_;
                            v___y_2485_ = v_a_2531_;
                            state = 3;
                            continue;
                        } else {
                            v___x_2538_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
                            leanh::lean_inc(v___y_2491_);
                            v___x_2539_ = l_Lean_Name_append(v___x_2538_, v___y_2491_);
                            v___x_2540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_2535_,
                                v_options_2533_,
                                v___x_2539_,
                            );
                            leanh::lean_dec(v___x_2539_);
                            if v___x_2540_ == 0 {
                                leanh::lean_del_object(v___x_2527_);
                                leanh::lean_dec(v___y_2497_);
                                leanh::lean_dec_ref(v___y_2496_);
                                leanh::lean_dec(v___y_2495_);
                                leanh::lean_dec_ref(v___y_2494_);
                                leanh::lean_dec(v___y_2491_);
                                v___y_2484_ = v___x_2537_;
                                v___y_2485_ = v_a_2531_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2541_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__9
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__9_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__9,
                                );
                                leanh::lean_inc(v___x_2537_);
                                v___x_2542_ = l_Nat_reprFast(v___x_2537_);
                                if v_isShared_2528_ == 0 {
                                    leanh::lean_ctor_set_tag(v___x_2527_, 3);
                                    leanh::lean_ctor_set(v___x_2527_, 0, v___x_2542_);
                                    v___x_2544_ = v___x_2527_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2560_ =
                                        leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                    leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_a_2531_);
                        leanh::lean_del_object(v___x_2527_);
                        leanh::lean_dec(v_numFields_2500_);
                        leanh::lean_dec(v___y_2497_);
                        leanh::lean_dec_ref(v___y_2496_);
                        leanh::lean_dec(v___y_2495_);
                        leanh::lean_dec_ref(v___y_2494_);
                        leanh::lean_dec(v___y_2491_);
                        v_a_2561_ = leanh::lean_ctor_get(v___x_2532_, 0);
                        v_isSharedCheck_2568_ =
                            (!leanh::lean_is_exclusive(v___x_2532_)) as u8;
                        if v_isSharedCheck_2568_ == 0 {
                            v___x_2563_ = v___x_2532_;
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2561_);
                            leanh::lean_dec(v___x_2532_);
                            v___x_2563_ = leanh::lean_box(0);
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2527_);
                    leanh::lean_dec(v_numFields_2500_);
                    leanh::lean_dec(v___y_2497_);
                    leanh::lean_dec_ref(v___y_2496_);
                    leanh::lean_dec(v___y_2495_);
                    leanh::lean_dec_ref(v___y_2494_);
                    leanh::lean_dec_ref(v___y_2493_);
                    leanh::lean_dec(v___y_2491_);
                    v_a_2569_ = leanh::lean_ctor_get(v___x_2530_, 0);
                    v_isSharedCheck_2576_ = (!leanh::lean_is_exclusive(v___x_2530_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2530_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2569_);
                        leanh::lean_dec(v___x_2530_);
                        v___x_2571_ = leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2545_ = l_Lean_MessageData_ofFormat(v___x_2544_);
                v___x_2546_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2546_, 0, v___x_2541_);
                leanh::lean_ctor_set(v___x_2546_, 1, v___x_2545_);
                v___x_2547_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__11_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__11,
                );
                v___x_2548_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2548_, 0, v___x_2546_);
                leanh::lean_ctor_set(v___x_2548_, 1, v___x_2547_);
                leanh::lean_inc(v_a_2531_);
                v___x_2549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2549_, 0, v_a_2531_);
                v___x_2550_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2550_, 0, v___x_2548_);
                leanh::lean_ctor_set(v___x_2550_, 1, v___x_2549_);
                v___x_2551_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                    v___y_2491_,
                    v___x_2550_,
                    v___y_2494_,
                    v___y_2495_,
                    v___y_2496_,
                    v___y_2497_,
                );
                leanh::lean_dec(v___y_2497_);
                leanh::lean_dec_ref(v___y_2496_);
                leanh::lean_dec(v___y_2495_);
                leanh::lean_dec_ref(v___y_2494_);
                if leanh::lean_obj_tag(v___x_2551_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2551_, 1);
                    v___y_2484_ = v___x_2537_;
                    v___y_2485_ = v_a_2531_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2537_);
                    leanh::lean_dec(v_a_2531_);
                    v_a_2552_ = leanh::lean_ctor_get(v___x_2551_, 0);
                    v_isSharedCheck_2559_ = (!leanh::lean_is_exclusive(v___x_2551_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2554_ = v___x_2551_;
                        v_isShared_2555_ = v_isSharedCheck_2559_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2552_);
                        leanh::lean_dec(v___x_2551_);
                        v___x_2554_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
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
                    v_reuseFailAlloc_2567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
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
                    v_reuseFailAlloc_2575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
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
                    v_reuseFailAlloc_2585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
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
                    v_reuseFailAlloc_2593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
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
                    v_reuseFailAlloc_2608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
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
                    v_reuseFailAlloc_2616_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
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
                    v_reuseFailAlloc_2624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
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
                    v_reuseFailAlloc_2632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
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
                v_foApprox_2646_ = leanh::lean_ctor_get_uint8(v___x_2645_, 0 as u32);
                v_ctxApprox_2647_ = leanh::lean_ctor_get_uint8(v___x_2645_, 1 as u32);
                v_quasiPatternApprox_2648_ =
                    leanh::lean_ctor_get_uint8(v___x_2645_, 2 as u32);
                v_constApprox_2649_ = leanh::lean_ctor_get_uint8(v___x_2645_, 3 as u32);
                v_isDefEqStuckEx_2650_ = leanh::lean_ctor_get_uint8(v___x_2645_, 4 as u32);
                v_unificationHints_2651_ = leanh::lean_ctor_get_uint8(v___x_2645_, 5 as u32);
                v_proofIrrelevance_2652_ = leanh::lean_ctor_get_uint8(v___x_2645_, 6 as u32);
                v_assignSyntheticOpaque_2653_ =
                    leanh::lean_ctor_get_uint8(v___x_2645_, 7 as u32);
                v_offsetCnstrs_2654_ = leanh::lean_ctor_get_uint8(v___x_2645_, 8 as u32);
                v_etaStruct_2655_ = leanh::lean_ctor_get_uint8(v___x_2645_, 10 as u32);
                v_univApprox_2656_ = leanh::lean_ctor_get_uint8(v___x_2645_, 11 as u32);
                v_iota_2657_ = leanh::lean_ctor_get_uint8(v___x_2645_, 12 as u32);
                v_beta_2658_ = leanh::lean_ctor_get_uint8(v___x_2645_, 13 as u32);
                v_proj_2659_ = leanh::lean_ctor_get_uint8(v___x_2645_, 14 as u32);
                v_zeta_2660_ = leanh::lean_ctor_get_uint8(v___x_2645_, 15 as u32);
                v_zetaDelta_2661_ = leanh::lean_ctor_get_uint8(v___x_2645_, 16 as u32);
                v_zetaUnused_2662_ = leanh::lean_ctor_get_uint8(v___x_2645_, 17 as u32);
                v_zetaHave_2663_ = leanh::lean_ctor_get_uint8(v___x_2645_, 18 as u32);
                v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v___x_2645_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v___x_2665_ = v___x_2645_;
                    v_isShared_2666_ = v_isSharedCheck_2736_;
                    state = 28;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2645_);
                    v___x_2665_ = leanh::lean_box(0);
                    v_isShared_2666_ = v_isSharedCheck_2736_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v_trackZetaDelta_2667_ = leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2668_ = leanh::lean_ctor_get(v___y_2641_, 1);
                v_lctx_2669_ = leanh::lean_ctor_get(v___y_2641_, 2);
                v_localInstances_2670_ = leanh::lean_ctor_get(v___y_2641_, 3);
                v_defEqCtx_x3f_2671_ = leanh::lean_ctor_get(v___y_2641_, 4);
                v_synthPendingDepth_2672_ = leanh::lean_ctor_get(v___y_2641_, 5);
                v_canUnfold_x3f_2673_ = leanh::lean_ctor_get(v___y_2641_, 6);
                v_univApprox_2674_ = leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2675_ = leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2676_ = leanh::lean_ctor_get_uint8(
                    v___y_2641_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2677_ = 1;
                if v_isShared_2666_ == 0 {
                    v_config_2679_ = v___x_2665_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        0 as u32,
                        v_foApprox_2646_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        1 as u32,
                        v_ctxApprox_2647_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        2 as u32,
                        v_quasiPatternApprox_2648_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        3 as u32,
                        v_constApprox_2649_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        4 as u32,
                        v_isDefEqStuckEx_2650_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        5 as u32,
                        v_unificationHints_2651_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        6 as u32,
                        v_proofIrrelevance_2652_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        7 as u32,
                        v_assignSyntheticOpaque_2653_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        8 as u32,
                        v_offsetCnstrs_2654_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        10 as u32,
                        v_etaStruct_2655_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        11 as u32,
                        v_univApprox_2656_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        12 as u32,
                        v_iota_2657_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        13 as u32,
                        v_beta_2658_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        14 as u32,
                        v_proj_2659_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        15 as u32,
                        v_zeta_2660_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        16 as u32,
                        v_zetaDelta_2661_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2735_,
                        17 as u32,
                        v_zetaUnused_2662_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_2679_, 9 as u32, v___x_2677_);
                v___x_2680_ = l_Lean_Meta_Context_configKey(v___y_2641_);
                v___x_2681_ = 3u64;
                v___x_2682_ = lean_uint64_shift_right(v___x_2680_, v___x_2681_);
                v___x_2683_ = lean_uint64_shift_left(v___x_2682_, v___x_2681_);
                v___x_2684_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Meta_injectionCore___lam__1___closed__14_once),
                    _init_l_Lean_Meta_injectionCore___lam__1___closed__14,
                );
                v_key_2685_ = lean_uint64_lor(v___x_2683_, v___x_2684_);
                v___x_2686_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2686_, 0, v_config_2679_);
                leanh::lean_ctor_set_uint64(
                    v___x_2686_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2685_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2673_);
                leanh::lean_inc(v_synthPendingDepth_2672_);
                leanh::lean_inc(v_defEqCtx_x3f_2671_);
                leanh::lean_inc_ref(v_localInstances_2670_);
                leanh::lean_inc_ref(v_lctx_2669_);
                leanh::lean_inc(v_zetaDeltaSet_2668_);
                v___x_2687_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2687_, 0, v___x_2686_);
                leanh::lean_ctor_set(v___x_2687_, 1, v_zetaDeltaSet_2668_);
                leanh::lean_ctor_set(v___x_2687_, 2, v_lctx_2669_);
                leanh::lean_ctor_set(v___x_2687_, 3, v_localInstances_2670_);
                leanh::lean_ctor_set(v___x_2687_, 4, v_defEqCtx_x3f_2671_);
                leanh::lean_ctor_set(v___x_2687_, 5, v_synthPendingDepth_2672_);
                leanh::lean_ctor_set(v___x_2687_, 6, v_canUnfold_x3f_2673_);
                leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2667_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2674_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2675_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
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
                leanh::lean_dec_ref_known(v___x_2687_, 7);
                if leanh::lean_obj_tag(v___x_2688_) == 0 {
                    v_a_2689_ = leanh::lean_ctor_get(v___x_2688_, 0);
                    leanh::lean_inc(v_a_2689_);
                    leanh::lean_dec_ref_known(v___x_2688_, 1);
                    leanh::lean_inc_ref(v___y_2635_);
                    leanh::lean_inc(v___y_2644_);
                    leanh::lean_inc_ref(v___y_2643_);
                    leanh::lean_inc(v___y_2642_);
                    leanh::lean_inc_ref(v___y_2641_);
                    v___x_2690_ = leanh::lean_apply_5(
                        v___y_2635_,
                        v___y_2641_,
                        v___y_2642_,
                        v___y_2643_,
                        v___y_2644_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = leanh::lean_ctor_get(v___x_2690_, 0);
                        leanh::lean_inc(v_a_2691_);
                        leanh::lean_dec_ref_known(v___x_2690_, 1);
                        v___x_2692_ = (leanh::lean_unbox(v_a_2691_) as u8);
                        leanh::lean_dec(v_a_2691_);
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
                            leanh::lean_inc(v___y_2644_);
                            leanh::lean_inc_ref(v___y_2643_);
                            leanh::lean_inc(v___y_2642_);
                            leanh::lean_inc_ref(v___y_2641_);
                            leanh::lean_inc(v_a_2689_);
                            v___x_2693_ = lean_infer_type(
                                v_a_2689_,
                                v___y_2641_,
                                v___y_2642_,
                                v___y_2643_,
                                v___y_2644_,
                            );
                            if leanh::lean_obj_tag(v___x_2693_) == 0 {
                                v_a_2694_ = leanh::lean_ctor_get(v___x_2693_, 0);
                                leanh::lean_inc(v_a_2694_);
                                leanh::lean_dec_ref_known(v___x_2693_, 1);
                                v___x_2695_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__16
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__16_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__16,
                                );
                                leanh::lean_inc(v_a_2689_);
                                v___x_2696_ = l_Lean_indentExpr(v_a_2689_);
                                v___x_2697_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2697_, 0, v___x_2695_);
                                leanh::lean_ctor_set(v___x_2697_, 1, v___x_2696_);
                                v___x_2698_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__18
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_injectionCore___lam__1___closed__18_once
                                    ),
                                    _init_l_Lean_Meta_injectionCore___lam__1___closed__18,
                                );
                                v___x_2699_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2699_, 0, v___x_2697_);
                                leanh::lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                                v___x_2700_ = l_Lean_indentExpr(v_a_2694_);
                                v___x_2701_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2701_, 0, v___x_2699_);
                                leanh::lean_ctor_set(v___x_2701_, 1, v___x_2700_);
                                leanh::lean_inc(v___y_2637_);
                                v___x_2702_ =
                                    l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                                        v___y_2637_,
                                        v___x_2701_,
                                        v___y_2641_,
                                        v___y_2642_,
                                        v___y_2643_,
                                        v___y_2644_,
                                    );
                                if leanh::lean_obj_tag(v___x_2702_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_2702_, 1);
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
                                    leanh::lean_dec(v_a_2689_);
                                    leanh::lean_dec(v___y_2644_);
                                    leanh::lean_dec_ref(v___y_2643_);
                                    leanh::lean_dec(v___y_2642_);
                                    leanh::lean_dec_ref(v___y_2641_);
                                    leanh::lean_dec_ref(v___y_2640_);
                                    leanh::lean_dec_ref(v___y_2639_);
                                    leanh::lean_dec(v___y_2637_);
                                    leanh::lean_dec_ref(v___y_2635_);
                                    leanh::lean_dec(v_fvarId_2462_);
                                    leanh::lean_dec(v___x_2461_);
                                    leanh::lean_dec(v_mvarId_2460_);
                                    v_a_2703_ = leanh::lean_ctor_get(v___x_2702_, 0);
                                    v_isSharedCheck_2710_ =
                                        (!leanh::lean_is_exclusive(v___x_2702_)) as u8;
                                    if v_isSharedCheck_2710_ == 0 {
                                        v___x_2705_ = v___x_2702_;
                                        v_isShared_2706_ = v_isSharedCheck_2710_;
                                        state = 30;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2703_);
                                        leanh::lean_dec(v___x_2702_);
                                        v___x_2705_ = leanh::lean_box(0);
                                        v_isShared_2706_ = v_isSharedCheck_2710_;
                                        state = 30;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_2689_);
                                leanh::lean_dec(v___y_2644_);
                                leanh::lean_dec_ref(v___y_2643_);
                                leanh::lean_dec(v___y_2642_);
                                leanh::lean_dec_ref(v___y_2641_);
                                leanh::lean_dec_ref(v___y_2640_);
                                leanh::lean_dec_ref(v___y_2639_);
                                leanh::lean_dec(v___y_2637_);
                                leanh::lean_dec_ref(v___y_2635_);
                                leanh::lean_dec(v_fvarId_2462_);
                                leanh::lean_dec(v___x_2461_);
                                leanh::lean_dec(v_mvarId_2460_);
                                v_a_2711_ = leanh::lean_ctor_get(v___x_2693_, 0);
                                v_isSharedCheck_2718_ =
                                    (!leanh::lean_is_exclusive(v___x_2693_)) as u8;
                                if v_isSharedCheck_2718_ == 0 {
                                    v___x_2713_ = v___x_2693_;
                                    v_isShared_2714_ = v_isSharedCheck_2718_;
                                    state = 32;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2711_);
                                    leanh::lean_dec(v___x_2693_);
                                    v___x_2713_ = leanh::lean_box(0);
                                    v_isShared_2714_ = v_isSharedCheck_2718_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2689_);
                        leanh::lean_dec(v___y_2644_);
                        leanh::lean_dec_ref(v___y_2643_);
                        leanh::lean_dec(v___y_2642_);
                        leanh::lean_dec_ref(v___y_2641_);
                        leanh::lean_dec_ref(v___y_2640_);
                        leanh::lean_dec_ref(v___y_2639_);
                        leanh::lean_dec(v___y_2637_);
                        leanh::lean_dec_ref(v___y_2635_);
                        leanh::lean_dec(v_fvarId_2462_);
                        leanh::lean_dec(v___x_2461_);
                        leanh::lean_dec(v_mvarId_2460_);
                        v_a_2719_ = leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2726_ =
                            (!leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2726_ == 0 {
                            v___x_2721_ = v___x_2690_;
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2719_);
                            leanh::lean_dec(v___x_2690_);
                            v___x_2721_ = leanh::lean_box(0);
                            v_isShared_2722_ = v_isSharedCheck_2726_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2644_);
                    leanh::lean_dec_ref(v___y_2643_);
                    leanh::lean_dec(v___y_2642_);
                    leanh::lean_dec_ref(v___y_2641_);
                    leanh::lean_dec_ref(v___y_2640_);
                    leanh::lean_dec_ref(v___y_2639_);
                    leanh::lean_dec(v___y_2637_);
                    leanh::lean_dec_ref(v___y_2635_);
                    leanh::lean_dec(v_fvarId_2462_);
                    leanh::lean_dec(v___x_2461_);
                    leanh::lean_dec(v_mvarId_2460_);
                    v_a_2727_ = leanh::lean_ctor_get(v___x_2688_, 0);
                    v_isSharedCheck_2734_ = (!leanh::lean_is_exclusive(v___x_2688_)) as u8;
                    if v_isSharedCheck_2734_ == 0 {
                        v___x_2729_ = v___x_2688_;
                        v_isShared_2730_ = v_isSharedCheck_2734_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2727_);
                        leanh::lean_dec(v___x_2688_);
                        v___x_2729_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2709_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
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
                    v_reuseFailAlloc_2717_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
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
                    v_reuseFailAlloc_2725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
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
                    v_reuseFailAlloc_2733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
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
                v___x_2745_ = leanh::lean_unsigned_to_nat(3);
                v___x_2746_ = l_Lean_Expr_isAppOfArity(v_type_2738_, v___x_2744_, v___x_2745_);
                if v___x_2746_ == 0 {
                    leanh::lean_dec_ref(v_prf_2739_);
                    leanh::lean_dec_ref(v_type_2738_);
                    leanh::lean_dec_ref(v___x_2463_);
                    leanh::lean_dec(v_fvarId_2462_);
                    v___x_2747_ = leanh::lean_obj_once(
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
                    leanh::lean_dec(v___y_2743_);
                    leanh::lean_dec_ref(v___y_2742_);
                    leanh::lean_dec(v___y_2741_);
                    leanh::lean_dec_ref(v___y_2740_);
                    return v___x_2748_;
                } else {
                    leanh::lean_inc(v_mvarId_2460_);
                    v___x_2749_ = l_Lean_MVarId_getType(
                        v_mvarId_2460_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    if leanh::lean_obj_tag(v___x_2749_) == 0 {
                        v_a_2750_ = leanh::lean_ctor_get(v___x_2749_, 0);
                        leanh::lean_inc(v_a_2750_);
                        leanh::lean_dec_ref_known(v___x_2749_, 1);
                        v___x_2751_ = l_Lean_Expr_appFn_x21(v_type_2738_);
                        v___x_2752_ = l_Lean_Expr_appArg_x21(v___x_2751_);
                        leanh::lean_dec_ref(v___x_2751_);
                        v___x_2753_ = l_Lean_Meta_isConstructorApp_x27_x3f(
                            v___x_2752_,
                            v___y_2740_,
                            v___y_2741_,
                            v___y_2742_,
                            v___y_2743_,
                        );
                        if leanh::lean_obj_tag(v___x_2753_) == 0 {
                            v_a_2754_ = leanh::lean_ctor_get(v___x_2753_, 0);
                            leanh::lean_inc(v_a_2754_);
                            leanh::lean_dec_ref_known(v___x_2753_, 1);
                            v___x_2755_ = l_Lean_Expr_appArg_x21(v_type_2738_);
                            leanh::lean_dec_ref(v_type_2738_);
                            v___x_2756_ = l_Lean_Meta_isConstructorApp_x27_x3f(
                                v___x_2755_,
                                v___y_2740_,
                                v___y_2741_,
                                v___y_2742_,
                                v___y_2743_,
                            );
                            if leanh::lean_obj_tag(v___x_2756_) == 0 {
                                if leanh::lean_obj_tag(v_a_2754_) == 1 {
                                    v_a_2757_ = leanh::lean_ctor_get(v___x_2756_, 0);
                                    leanh::lean_inc(v_a_2757_);
                                    leanh::lean_dec_ref_known(v___x_2756_, 1);
                                    if leanh::lean_obj_tag(v_a_2757_) == 1 {
                                        v_val_2758_ = leanh::lean_ctor_get(v_a_2754_, 0);
                                        leanh::lean_inc(v_val_2758_);
                                        leanh::lean_dec_ref_known(v_a_2754_, 1);
                                        v_val_2759_ = leanh::lean_ctor_get(v_a_2757_, 0);
                                        leanh::lean_inc(v_val_2759_);
                                        leanh::lean_dec_ref_known(v_a_2757_, 1);
                                        v___x_2760_ =
                                            l_Lean_Meta_injectionCore___lam__1___closed__25;
                                        v___x_2761_ =
                                            l_Lean_Meta_injectionCore___lam__1___closed__26;
                                        v___x_2762_ = l_Lean_Name_mkStr3(
                                            v___x_2760_,
                                            v___x_2761_,
                                            v___x_2463_,
                                        );
                                        leanh::lean_inc_n(v___x_2762_, 2);
                                        v___f_2763_ = leanh::lean_alloc_closure(
                                            l_Lean_Meta_injectionCore___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            6,
                                            1,
                                        );
                                        leanh::lean_closure_set(v___f_2763_, 0, v___x_2762_);
                                        v___x_2764_ = l_Lean_Meta_injectionCore___lam__0(
                                            v___x_2762_,
                                            v___y_2740_,
                                            v___y_2741_,
                                            v___y_2742_,
                                            v___y_2743_,
                                        );
                                        v_a_2765_ = leanh::lean_ctor_get(v___x_2764_, 0);
                                        v_isSharedCheck_2798_ =
                                            (!leanh::lean_is_exclusive(v___x_2764_)) as u8;
                                        if v_isSharedCheck_2798_ == 0 {
                                            v___x_2767_ = v___x_2764_;
                                            v_isShared_2768_ = v_isSharedCheck_2798_;
                                            state = 39;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2765_);
                                            leanh::lean_dec(v___x_2764_);
                                            v___x_2767_ = leanh::lean_box(0);
                                            v_isShared_2768_ = v_isSharedCheck_2798_;
                                            state = 39;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_2757_);
                                        leanh::lean_dec_ref_known(v_a_2754_, 1);
                                        leanh::lean_dec(v_a_2750_);
                                        leanh::lean_dec_ref(v_prf_2739_);
                                        leanh::lean_dec_ref(v___x_2463_);
                                        leanh::lean_dec(v_fvarId_2462_);
                                        v___y_2477_ = v___y_2740_;
                                        v___y_2478_ = v___y_2741_;
                                        v___y_2479_ = v___y_2742_;
                                        v___y_2480_ = v___y_2743_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v___x_2756_, 1);
                                    leanh::lean_dec(v_a_2754_);
                                    leanh::lean_dec(v_a_2750_);
                                    leanh::lean_dec_ref(v_prf_2739_);
                                    leanh::lean_dec_ref(v___x_2463_);
                                    leanh::lean_dec(v_fvarId_2462_);
                                    v___y_2477_ = v___y_2740_;
                                    v___y_2478_ = v___y_2741_;
                                    v___y_2479_ = v___y_2742_;
                                    v___y_2480_ = v___y_2743_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_2754_);
                                leanh::lean_dec(v_a_2750_);
                                leanh::lean_dec(v___y_2743_);
                                leanh::lean_dec_ref(v___y_2742_);
                                leanh::lean_dec(v___y_2741_);
                                leanh::lean_dec_ref(v___y_2740_);
                                leanh::lean_dec_ref(v_prf_2739_);
                                leanh::lean_dec_ref(v___x_2463_);
                                leanh::lean_dec(v_fvarId_2462_);
                                leanh::lean_dec(v___x_2461_);
                                leanh::lean_dec(v_mvarId_2460_);
                                v_a_2799_ = leanh::lean_ctor_get(v___x_2756_, 0);
                                v_isSharedCheck_2806_ =
                                    (!leanh::lean_is_exclusive(v___x_2756_)) as u8;
                                if v_isSharedCheck_2806_ == 0 {
                                    v___x_2801_ = v___x_2756_;
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 45;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2799_);
                                    leanh::lean_dec(v___x_2756_);
                                    v___x_2801_ = leanh::lean_box(0);
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 45;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2750_);
                            leanh::lean_dec(v___y_2743_);
                            leanh::lean_dec_ref(v___y_2742_);
                            leanh::lean_dec(v___y_2741_);
                            leanh::lean_dec_ref(v___y_2740_);
                            leanh::lean_dec_ref(v_prf_2739_);
                            leanh::lean_dec_ref(v_type_2738_);
                            leanh::lean_dec_ref(v___x_2463_);
                            leanh::lean_dec(v_fvarId_2462_);
                            leanh::lean_dec(v___x_2461_);
                            leanh::lean_dec(v_mvarId_2460_);
                            v_a_2807_ = leanh::lean_ctor_get(v___x_2753_, 0);
                            v_isSharedCheck_2814_ =
                                (!leanh::lean_is_exclusive(v___x_2753_)) as u8;
                            if v_isSharedCheck_2814_ == 0 {
                                v___x_2809_ = v___x_2753_;
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 47;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2807_);
                                leanh::lean_dec(v___x_2753_);
                                v___x_2809_ = leanh::lean_box(0);
                                v_isShared_2810_ = v_isSharedCheck_2814_;
                                state = 47;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_2743_);
                        leanh::lean_dec_ref(v___y_2742_);
                        leanh::lean_dec(v___y_2741_);
                        leanh::lean_dec_ref(v___y_2740_);
                        leanh::lean_dec_ref(v_prf_2739_);
                        leanh::lean_dec_ref(v_type_2738_);
                        leanh::lean_dec_ref(v___x_2463_);
                        leanh::lean_dec(v_fvarId_2462_);
                        leanh::lean_dec(v___x_2461_);
                        leanh::lean_dec(v_mvarId_2460_);
                        v_a_2815_ = leanh::lean_ctor_get(v___x_2749_, 0);
                        v_isSharedCheck_2822_ =
                            (!leanh::lean_is_exclusive(v___x_2749_)) as u8;
                        if v_isSharedCheck_2822_ == 0 {
                            v___x_2817_ = v___x_2749_;
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 49;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2815_);
                            leanh::lean_dec(v___x_2749_);
                            v___x_2817_ = leanh::lean_box(0);
                            v_isShared_2818_ = v_isSharedCheck_2822_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            39 => {
                v___x_2769_ = (leanh::lean_unbox(v_a_2765_) as u8);
                leanh::lean_dec(v_a_2765_);
                if v___x_2769_ == 0 {
                    leanh::lean_del_object(v___x_2767_);
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
                    leanh::lean_inc(v___y_2743_);
                    leanh::lean_inc_ref(v___y_2742_);
                    leanh::lean_inc(v___y_2741_);
                    leanh::lean_inc_ref(v___y_2740_);
                    leanh::lean_inc_ref(v_prf_2739_);
                    v___x_2770_ = lean_infer_type(
                        v_prf_2739_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                    );
                    if leanh::lean_obj_tag(v___x_2770_) == 0 {
                        v_a_2771_ = leanh::lean_ctor_get(v___x_2770_, 0);
                        leanh::lean_inc(v_a_2771_);
                        leanh::lean_dec_ref_known(v___x_2770_, 1);
                        v___x_2772_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__28
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__28_once
                            ),
                            _init_l_Lean_Meta_injectionCore___lam__1___closed__28,
                        );
                        v___x_2773_ = l_Lean_MessageData_ofExpr(v_a_2771_);
                        v___x_2774_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2774_, 0, v___x_2772_);
                        leanh::lean_ctor_set(v___x_2774_, 1, v___x_2773_);
                        v___x_2775_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_injectionCore___lam__1___closed__30_once
                            ),
                            _init_l_Lean_Meta_injectionCore___lam__1___closed__30,
                        );
                        v___x_2776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2776_, 0, v___x_2774_);
                        leanh::lean_ctor_set(v___x_2776_, 1, v___x_2775_);
                        leanh::lean_inc(v_mvarId_2460_);
                        if v_isShared_2768_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2767_, 1);
                            leanh::lean_ctor_set(v___x_2767_, 0, v_mvarId_2460_);
                            v___x_2778_ = v___x_2767_;
                            state = 40;
                            continue;
                        } else {
                            v_reuseFailAlloc_2789_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_mvarId_2460_);
                            v___x_2778_ = v_reuseFailAlloc_2789_;
                            state = 40;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2767_);
                        leanh::lean_dec_ref(v___f_2763_);
                        leanh::lean_dec(v___x_2762_);
                        leanh::lean_dec(v_val_2759_);
                        leanh::lean_dec(v_val_2758_);
                        leanh::lean_dec(v_a_2750_);
                        leanh::lean_dec(v___y_2743_);
                        leanh::lean_dec_ref(v___y_2742_);
                        leanh::lean_dec(v___y_2741_);
                        leanh::lean_dec_ref(v___y_2740_);
                        leanh::lean_dec_ref(v_prf_2739_);
                        leanh::lean_dec(v_fvarId_2462_);
                        leanh::lean_dec(v___x_2461_);
                        leanh::lean_dec(v_mvarId_2460_);
                        v_a_2790_ = leanh::lean_ctor_get(v___x_2770_, 0);
                        v_isSharedCheck_2797_ =
                            (!leanh::lean_is_exclusive(v___x_2770_)) as u8;
                        if v_isSharedCheck_2797_ == 0 {
                            v___x_2792_ = v___x_2770_;
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2790_);
                            leanh::lean_dec(v___x_2770_);
                            v___x_2792_ = leanh::lean_box(0);
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 43;
                            continue;
                        }
                    }
                }
            }
            40 => {
                v___x_2779_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2779_, 0, v___x_2776_);
                leanh::lean_ctor_set(v___x_2779_, 1, v___x_2778_);
                leanh::lean_inc(v___x_2762_);
                v___x_2780_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                    v___x_2762_,
                    v___x_2779_,
                    v___y_2740_,
                    v___y_2741_,
                    v___y_2742_,
                    v___y_2743_,
                );
                if leanh::lean_obj_tag(v___x_2780_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2780_, 1);
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
                    leanh::lean_dec_ref(v___f_2763_);
                    leanh::lean_dec(v___x_2762_);
                    leanh::lean_dec(v_val_2759_);
                    leanh::lean_dec(v_val_2758_);
                    leanh::lean_dec(v_a_2750_);
                    leanh::lean_dec(v___y_2743_);
                    leanh::lean_dec_ref(v___y_2742_);
                    leanh::lean_dec(v___y_2741_);
                    leanh::lean_dec_ref(v___y_2740_);
                    leanh::lean_dec_ref(v_prf_2739_);
                    leanh::lean_dec(v_fvarId_2462_);
                    leanh::lean_dec(v___x_2461_);
                    leanh::lean_dec(v_mvarId_2460_);
                    v_a_2781_ = leanh::lean_ctor_get(v___x_2780_, 0);
                    v_isSharedCheck_2788_ = (!leanh::lean_is_exclusive(v___x_2780_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2783_ = v___x_2780_;
                        v_isShared_2784_ = v_isSharedCheck_2788_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2781_);
                        leanh::lean_dec(v___x_2780_);
                        v___x_2783_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
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
                    v_reuseFailAlloc_2796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
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
                    v_reuseFailAlloc_2805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
                    v_reuseFailAlloc_2813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
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
                    v_reuseFailAlloc_2821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
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
                    v_reuseFailAlloc_2853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
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
                    v_reuseFailAlloc_2861_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
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
                    v_reuseFailAlloc_2869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
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
                    v_reuseFailAlloc_2877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
                    v_reuseFailAlloc_2885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
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
                    v_reuseFailAlloc_2893_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
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
    mut v_mvarId_2895_: *mut leanh::LeanObject,
    mut v___x_2896_: *mut leanh::LeanObject,
    mut v_fvarId_2897_: *mut leanh::LeanObject,
    mut v___x_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
    mut v___y_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_2908_: *mut leanh::LeanObject,
    mut v_fvarId_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Meta_injectionCore___closed__0;
    v___x_2916_ = l_Lean_Meta_injectionCore___closed__1;
    leanh::lean_inc(v_mvarId_2908_);
    v___f_2917_ = leanh::lean_alloc_closure(
        l_Lean_Meta_injectionCore___lam__1___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_2917_, 0, v_mvarId_2908_);
    leanh::lean_closure_set(v___f_2917_, 1, v___x_2916_);
    leanh::lean_closure_set(v___f_2917_, 2, v_fvarId_2909_);
    leanh::lean_closure_set(v___f_2917_, 3, v___x_2915_);
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
    mut v_mvarId_2919_: *mut leanh::LeanObject,
    mut v_fvarId_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
    mut v_a_2922_: *mut leanh::LeanObject,
    mut v_a_2923_: *mut leanh::LeanObject,
    mut v_a_2924_: *mut leanh::LeanObject,
    mut v_a_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Lean_Meta_injectionCore(
        v_mvarId_2919_,
        v_fvarId_2920_,
        v_a_2921_,
        v_a_2922_,
        v_a_2923_,
        v_a_2924_,
    );
    leanh::lean_dec(v_a_2924_);
    leanh::lean_dec_ref(v_a_2923_);
    leanh::lean_dec(v_a_2922_);
    leanh::lean_dec_ref(v_a_2921_);
    return v_res_2926_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(
    mut v_mvarId_2927_: *mut leanh::LeanObject,
    mut v_val_2928_: *mut leanh::LeanObject,
    mut v___y_2929_: *mut leanh::LeanObject,
    mut v___y_2930_: *mut leanh::LeanObject,
    mut v___y_2931_: *mut leanh::LeanObject,
    mut v___y_2932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2934_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___redArg(
        v_mvarId_2927_,
        v_val_2928_,
        v___y_2930_,
    );
    return v___x_2934_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0___boxed(
    mut v_mvarId_2935_: *mut leanh::LeanObject,
    mut v_val_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v___y_2940_: *mut leanh::LeanObject,
    mut v___y_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2942_ = l_Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0(
        v_mvarId_2935_,
        v_val_2936_,
        v___y_2937_,
        v___y_2938_,
        v___y_2939_,
        v___y_2940_,
    );
    leanh::lean_dec(v___y_2940_);
    leanh::lean_dec_ref(v___y_2939_);
    leanh::lean_dec(v___y_2938_);
    leanh::lean_dec_ref(v___y_2937_);
    return v_res_2942_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0(
    mut v_00_u03b2_2943_: *mut leanh::LeanObject,
    mut v_x_2944_: *mut leanh::LeanObject,
    mut v_x_2945_: *mut leanh::LeanObject,
    mut v_x_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0___redArg(v_x_2944_, v_x_2945_, v_x_2946_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2948_: *mut leanh::LeanObject,
    mut v_x_2949_: *mut leanh::LeanObject,
    mut v_x_2950_: usize,
    mut v_x_2951_: usize,
    mut v_x_2952_: *mut leanh::LeanObject,
    mut v_x_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___redArg(v_x_2949_, v_x_2950_, v_x_2951_, v_x_2952_, v_x_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2955_: *mut leanh::LeanObject,
    mut v_x_2956_: *mut leanh::LeanObject,
    mut v_x_2957_: *mut leanh::LeanObject,
    mut v_x_2958_: *mut leanh::LeanObject,
    mut v_x_2959_: *mut leanh::LeanObject,
    mut v_x_2960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17908__boxed_2961_: usize = 0;
    let mut v_x_17909__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17908__boxed_2961_ = leanh::lean_unbox_usize(v_x_2957_);
    leanh::lean_dec(v_x_2957_);
    v_x_17909__boxed_2962_ = leanh::lean_unbox_usize(v_x_2958_);
    leanh::lean_dec(v_x_2958_);
    v_res_2963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2(v_00_u03b2_2955_, v_x_2956_, v_x_17908__boxed_2961_, v_x_17909__boxed_2962_, v_x_2959_, v_x_2960_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_2964_: *mut leanh::LeanObject,
    mut v_n_2965_: *mut leanh::LeanObject,
    mut v_k_2966_: *mut leanh::LeanObject,
    mut v_v_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5___redArg(v_n_2965_, v_k_2966_, v_v_2967_);
    return v___x_2968_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_2969_: *mut leanh::LeanObject,
    mut v_depth_2970_: usize,
    mut v_keys_2971_: *mut leanh::LeanObject,
    mut v_vals_2972_: *mut leanh::LeanObject,
    mut v_heq_2973_: *mut leanh::LeanObject,
    mut v_i_2974_: *mut leanh::LeanObject,
    mut v_entries_2975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_2970_, v_keys_2971_, v_vals_2972_, v_i_2974_, v_entries_2975_);
    return v___x_2976_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_2977_: *mut leanh::LeanObject,
    mut v_depth_2978_: *mut leanh::LeanObject,
    mut v_keys_2979_: *mut leanh::LeanObject,
    mut v_vals_2980_: *mut leanh::LeanObject,
    mut v_heq_2981_: *mut leanh::LeanObject,
    mut v_i_2982_: *mut leanh::LeanObject,
    mut v_entries_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2984_: usize = 0;
    let mut v_res_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2984_ = leanh::lean_unbox_usize(v_depth_2978_);
    leanh::lean_dec(v_depth_2978_);
    v_res_2985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_2977_, v_depth_boxed_2984_, v_keys_2979_, v_vals_2980_, v_heq_2981_, v_i_2982_, v_entries_2983_);
    leanh::lean_dec_ref(v_vals_2980_);
    leanh::lean_dec_ref(v_keys_2979_);
    return v_res_2985_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_2986_: *mut leanh::LeanObject,
    mut v_x_2987_: *mut leanh::LeanObject,
    mut v_x_2988_: *mut leanh::LeanObject,
    mut v_x_2989_: *mut leanh::LeanObject,
    mut v_x_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_injectionCore_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_2987_, v_x_2988_, v_x_2989_, v_x_2990_);
    return v___x_2991_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorIdx(
    mut v_x_2992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2992_) == 0 {
        let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2993_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2993_;
    } else {
        let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2994_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2994_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorIdx___boxed(
    mut v_x_2995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2996_ = l_Lean_Meta_InjectionResult_ctorIdx(v_x_2995_);
    leanh::lean_dec(v_x_2995_);
    return v_res_2996_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim___redArg(
    mut v_t_2997_: *mut leanh::LeanObject,
    mut v_k_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2997_) == 0 {
        return v_k_2998_;
    } else {
        let mut v_mvarId_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_newEqs_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_remainingNames_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_2999_ = leanh::lean_ctor_get(v_t_2997_, 0);
        leanh::lean_inc(v_mvarId_2999_);
        v_newEqs_3000_ = leanh::lean_ctor_get(v_t_2997_, 1);
        leanh::lean_inc_ref(v_newEqs_3000_);
        v_remainingNames_3001_ = leanh::lean_ctor_get(v_t_2997_, 2);
        leanh::lean_inc(v_remainingNames_3001_);
        leanh::lean_dec_ref_known(v_t_2997_, 3);
        v___x_3002_ = leanh::lean_apply_3(
            v_k_2998_,
            v_mvarId_2999_,
            v_newEqs_3000_,
            v_remainingNames_3001_,
        );
        return v___x_3002_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim(
    mut v_motive_3003_: *mut leanh::LeanObject,
    mut v_ctorIdx_3004_: *mut leanh::LeanObject,
    mut v_t_3005_: *mut leanh::LeanObject,
    mut v_h_3006_: *mut leanh::LeanObject,
    mut v_k_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3005_, v_k_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_ctorElim___boxed(
    mut v_motive_3009_: *mut leanh::LeanObject,
    mut v_ctorIdx_3010_: *mut leanh::LeanObject,
    mut v_t_3011_: *mut leanh::LeanObject,
    mut v_h_3012_: *mut leanh::LeanObject,
    mut v_k_3013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3014_ = l_Lean_Meta_InjectionResult_ctorElim(
        v_motive_3009_,
        v_ctorIdx_3010_,
        v_t_3011_,
        v_h_3012_,
        v_k_3013_,
    );
    leanh::lean_dec(v_ctorIdx_3010_);
    return v_res_3014_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_solved_elim___redArg(
    mut v_t_3015_: *mut leanh::LeanObject,
    mut v_solved_3016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3015_, v_solved_3016_);
    return v___x_3017_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_solved_elim(
    mut v_motive_3018_: *mut leanh::LeanObject,
    mut v_t_3019_: *mut leanh::LeanObject,
    mut v_h_3020_: *mut leanh::LeanObject,
    mut v_solved_3021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3022_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3019_, v_solved_3021_);
    return v___x_3022_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_subgoal_elim___redArg(
    mut v_t_3023_: *mut leanh::LeanObject,
    mut v_subgoal_3024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3023_, v_subgoal_3024_);
    return v___x_3025_;
}
pub unsafe fn l_Lean_Meta_InjectionResult_subgoal_elim(
    mut v_motive_3026_: *mut leanh::LeanObject,
    mut v_t_3027_: *mut leanh::LeanObject,
    mut v_h_3028_: *mut leanh::LeanObject,
    mut v_subgoal_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = l_Lean_Meta_InjectionResult_ctorElim___redArg(v_t_3027_, v_subgoal_3029_);
    return v___x_3030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injectionIntro_go(
    mut v_tryToClear_3031_: u8,
    mut v_a_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
    mut v_a_3036_: *mut leanh::LeanObject,
    mut v_a_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3042_: u8 = 0;
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3064_: u8 = 0;
    let mut v_a_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3068_: u8 = 0;
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_head_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_a_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3041_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3042_ = lean_nat_dec_eq(v_a_3032_, v_zero_3041_);
                if v_isZero_3042_ == 1 {
                    leanh::lean_dec(v_a_3032_);
                    v___x_3043_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3043_, 0, v_a_3033_);
                    leanh::lean_ctor_set(v___x_3043_, 1, v_a_3034_);
                    leanh::lean_ctor_set(v___x_3043_, 2, v_a_3035_);
                    v___x_3044_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
                    return v___x_3044_;
                } else {
                    v_one_3045_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3046_ = lean_nat_sub(v_a_3032_, v_one_3045_);
                    leanh::lean_dec(v_a_3032_);
                    if leanh::lean_obj_tag(v_a_3035_) == 0 {
                        v___x_3047_ = l_Lean_Meta_intro1Core(
                            v_a_3033_,
                            v_isZero_3042_,
                            v_a_3036_,
                            v_a_3037_,
                            v_a_3038_,
                            v_a_3039_,
                        );
                        if leanh::lean_obj_tag(v___x_3047_) == 0 {
                            v_a_3048_ = leanh::lean_ctor_get(v___x_3047_, 0);
                            leanh::lean_inc(v_a_3048_);
                            leanh::lean_dec_ref_known(v___x_3047_, 1);
                            v_fst_3049_ = leanh::lean_ctor_get(v_a_3048_, 0);
                            leanh::lean_inc(v_fst_3049_);
                            v_snd_3050_ = leanh::lean_ctor_get(v_a_3048_, 1);
                            leanh::lean_inc(v_snd_3050_);
                            leanh::lean_dec(v_a_3048_);
                            v___x_3051_ = l_Lean_Meta_heqToEq(
                                v_snd_3050_,
                                v_fst_3049_,
                                v_tryToClear_3031_,
                                v_a_3036_,
                                v_a_3037_,
                                v_a_3038_,
                                v_a_3039_,
                            );
                            if leanh::lean_obj_tag(v___x_3051_) == 0 {
                                v_a_3052_ = leanh::lean_ctor_get(v___x_3051_, 0);
                                leanh::lean_inc(v_a_3052_);
                                leanh::lean_dec_ref_known(v___x_3051_, 1);
                                v_fst_3053_ = leanh::lean_ctor_get(v_a_3052_, 0);
                                leanh::lean_inc(v_fst_3053_);
                                v_snd_3054_ = leanh::lean_ctor_get(v_a_3052_, 1);
                                leanh::lean_inc(v_snd_3054_);
                                leanh::lean_dec(v_a_3052_);
                                v___x_3055_ = lean_array_push(v_a_3034_, v_fst_3053_);
                                v_a_3032_ = v_n_3046_;
                                v_a_3033_ = v_snd_3054_;
                                v_a_3034_ = v___x_3055_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_n_3046_);
                                leanh::lean_dec_ref(v_a_3034_);
                                v_a_3057_ = leanh::lean_ctor_get(v___x_3051_, 0);
                                v_isSharedCheck_3064_ =
                                    (!leanh::lean_is_exclusive(v___x_3051_)) as u8;
                                if v_isSharedCheck_3064_ == 0 {
                                    v___x_3059_ = v___x_3051_;
                                    v_isShared_3060_ = v_isSharedCheck_3064_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3057_);
                                    leanh::lean_dec(v___x_3051_);
                                    v___x_3059_ = leanh::lean_box(0);
                                    v_isShared_3060_ = v_isSharedCheck_3064_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_n_3046_);
                            leanh::lean_dec_ref(v_a_3034_);
                            v_a_3065_ = leanh::lean_ctor_get(v___x_3047_, 0);
                            v_isSharedCheck_3072_ =
                                (!leanh::lean_is_exclusive(v___x_3047_)) as u8;
                            if v_isSharedCheck_3072_ == 0 {
                                v___x_3067_ = v___x_3047_;
                                v_isShared_3068_ = v_isSharedCheck_3072_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3065_);
                                leanh::lean_dec(v___x_3047_);
                                v___x_3067_ = leanh::lean_box(0);
                                v_isShared_3068_ = v_isSharedCheck_3072_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_head_3073_ = leanh::lean_ctor_get(v_a_3035_, 0);
                        leanh::lean_inc(v_head_3073_);
                        v_tail_3074_ = leanh::lean_ctor_get(v_a_3035_, 1);
                        leanh::lean_inc(v_tail_3074_);
                        leanh::lean_dec_ref_known(v_a_3035_, 2);
                        v___x_3075_ = l_Lean_MVarId_intro(
                            v_a_3033_,
                            v_head_3073_,
                            v_a_3036_,
                            v_a_3037_,
                            v_a_3038_,
                            v_a_3039_,
                        );
                        if leanh::lean_obj_tag(v___x_3075_) == 0 {
                            v_a_3076_ = leanh::lean_ctor_get(v___x_3075_, 0);
                            leanh::lean_inc(v_a_3076_);
                            leanh::lean_dec_ref_known(v___x_3075_, 1);
                            v_fst_3077_ = leanh::lean_ctor_get(v_a_3076_, 0);
                            leanh::lean_inc(v_fst_3077_);
                            v_snd_3078_ = leanh::lean_ctor_get(v_a_3076_, 1);
                            leanh::lean_inc(v_snd_3078_);
                            leanh::lean_dec(v_a_3076_);
                            v___x_3079_ = l_Lean_Meta_heqToEq(
                                v_snd_3078_,
                                v_fst_3077_,
                                v_tryToClear_3031_,
                                v_a_3036_,
                                v_a_3037_,
                                v_a_3038_,
                                v_a_3039_,
                            );
                            if leanh::lean_obj_tag(v___x_3079_) == 0 {
                                v_a_3080_ = leanh::lean_ctor_get(v___x_3079_, 0);
                                leanh::lean_inc(v_a_3080_);
                                leanh::lean_dec_ref_known(v___x_3079_, 1);
                                v_fst_3081_ = leanh::lean_ctor_get(v_a_3080_, 0);
                                leanh::lean_inc(v_fst_3081_);
                                v_snd_3082_ = leanh::lean_ctor_get(v_a_3080_, 1);
                                leanh::lean_inc(v_snd_3082_);
                                leanh::lean_dec(v_a_3080_);
                                v___x_3083_ = lean_array_push(v_a_3034_, v_fst_3081_);
                                v_a_3032_ = v_n_3046_;
                                v_a_3033_ = v_snd_3082_;
                                v_a_3034_ = v___x_3083_;
                                v_a_3035_ = v_tail_3074_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_tail_3074_);
                                leanh::lean_dec(v_n_3046_);
                                leanh::lean_dec_ref(v_a_3034_);
                                v_a_3085_ = leanh::lean_ctor_get(v___x_3079_, 0);
                                v_isSharedCheck_3092_ =
                                    (!leanh::lean_is_exclusive(v___x_3079_)) as u8;
                                if v_isSharedCheck_3092_ == 0 {
                                    v___x_3087_ = v___x_3079_;
                                    v_isShared_3088_ = v_isSharedCheck_3092_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3085_);
                                    leanh::lean_dec(v___x_3079_);
                                    v___x_3087_ = leanh::lean_box(0);
                                    v_isShared_3088_ = v_isSharedCheck_3092_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_tail_3074_);
                            leanh::lean_dec(v_n_3046_);
                            leanh::lean_dec_ref(v_a_3034_);
                            v_a_3093_ = leanh::lean_ctor_get(v___x_3075_, 0);
                            v_isSharedCheck_3100_ =
                                (!leanh::lean_is_exclusive(v___x_3075_)) as u8;
                            if v_isSharedCheck_3100_ == 0 {
                                v___x_3095_ = v___x_3075_;
                                v_isShared_3096_ = v_isSharedCheck_3100_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3093_);
                                leanh::lean_dec(v___x_3075_);
                                v___x_3095_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
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
                    v_reuseFailAlloc_3071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
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
                    v_reuseFailAlloc_3091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
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
                    v_reuseFailAlloc_3099_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
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
    mut v_tryToClear_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
    mut v_a_3104_: *mut leanh::LeanObject,
    mut v_a_3105_: *mut leanh::LeanObject,
    mut v_a_3106_: *mut leanh::LeanObject,
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
    mut v_a_3109_: *mut leanh::LeanObject,
    mut v_a_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryToClear_boxed_3111_: u8 = 0;
    let mut v_res_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryToClear_boxed_3111_ = (leanh::lean_unbox(v_tryToClear_3101_) as u8);
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
    leanh::lean_dec(v_a_3109_);
    leanh::lean_dec_ref(v_a_3108_);
    leanh::lean_dec(v_a_3107_);
    leanh::lean_dec_ref(v_a_3106_);
    return v_res_3112_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__2() -> *mut leanh::LeanObject {
    let mut v_cls_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_3119_ = l_Lean_Meta_injectionIntro___closed__1;
    v___x_3120_ = l_Lean_Meta_injectionCore___lam__0___closed__1;
    v___x_3121_ = l_Lean_Name_append(v___x_3120_, v_cls_3119_);
    return v___x_3121_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_Meta_injectionIntro___closed__3;
    v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
    return v___x_3124_;
}
pub unsafe fn _init_l_Lean_Meta_injectionIntro___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ = l_Lean_Meta_injectionIntro___closed__5;
    v___x_3127_ = l_Lean_stringToMessageData(v___x_3126_);
    return v___x_3127_;
}
pub unsafe fn l_Lean_Meta_injectionIntro(
    mut v_mvarId_3128_: *mut leanh::LeanObject,
    mut v_numEqs_3129_: *mut leanh::LeanObject,
    mut v_newNames_3130_: *mut leanh::LeanObject,
    mut v_tryToClear_3131_: u8,
    mut v_a_3132_: *mut leanh::LeanObject,
    mut v_a_3133_: *mut leanh::LeanObject,
    mut v_a_3134_: *mut leanh::LeanObject,
    mut v_a_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3145_: u8 = 0;
    let mut v_inheritedTraceOptions_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3144_ = leanh::lean_ctor_get(v_a_3134_, 2);
                v_hasTrace_3145_ = leanh::lean_ctor_get_uint8(
                    v_options_3144_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3145_ == 0 {
                    v___y_3138_ = v_a_3132_;
                    v___y_3139_ = v_a_3133_;
                    v___y_3140_ = v_a_3134_;
                    v___y_3141_ = v_a_3135_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_3146_ = leanh::lean_ctor_get(v_a_3134_, 13);
                    v_cls_3147_ = l_Lean_Meta_injectionIntro___closed__1;
                    v___x_3148_ = leanh::lean_obj_once(
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
                        v___x_3150_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__4_once),
                            _init_l_Lean_Meta_injectionIntro___closed__4,
                        );
                        leanh::lean_inc(v_numEqs_3129_);
                        v___x_3151_ = l_Nat_reprFast(v_numEqs_3129_);
                        v___x_3152_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3152_, 0, v___x_3151_);
                        v___x_3153_ = l_Lean_MessageData_ofFormat(v___x_3152_);
                        v___x_3154_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3154_, 0, v___x_3150_);
                        leanh::lean_ctor_set(v___x_3154_, 1, v___x_3153_);
                        v___x_3155_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__6),
                            core::ptr::addr_of_mut!(l_Lean_Meta_injectionIntro___closed__6_once),
                            _init_l_Lean_Meta_injectionIntro___closed__6,
                        );
                        v___x_3156_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3156_, 0, v___x_3154_);
                        leanh::lean_ctor_set(v___x_3156_, 1, v___x_3155_);
                        leanh::lean_inc(v_mvarId_3128_);
                        v___x_3157_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3157_, 0, v_mvarId_3128_);
                        v___x_3158_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3158_, 0, v___x_3156_);
                        leanh::lean_ctor_set(v___x_3158_, 1, v___x_3157_);
                        v___x_3159_ = l_Lean_addTrace___at___00Lean_Meta_injectionCore_spec__1(
                            v_cls_3147_,
                            v___x_3158_,
                            v_a_3132_,
                            v_a_3133_,
                            v_a_3134_,
                            v_a_3135_,
                        );
                        if leanh::lean_obj_tag(v___x_3159_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3159_, 1);
                            v___y_3138_ = v_a_3132_;
                            v___y_3139_ = v_a_3133_;
                            v___y_3140_ = v_a_3134_;
                            v___y_3141_ = v_a_3135_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_newNames_3130_);
                            leanh::lean_dec(v_numEqs_3129_);
                            leanh::lean_dec(v_mvarId_3128_);
                            v_a_3160_ = leanh::lean_ctor_get(v___x_3159_, 0);
                            v_isSharedCheck_3167_ =
                                (!leanh::lean_is_exclusive(v___x_3159_)) as u8;
                            if v_isSharedCheck_3167_ == 0 {
                                v___x_3162_ = v___x_3159_;
                                v_isShared_3163_ = v_isSharedCheck_3167_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3160_);
                                leanh::lean_dec(v___x_3159_);
                                v___x_3162_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
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
    mut v_mvarId_3168_: *mut leanh::LeanObject,
    mut v_numEqs_3169_: *mut leanh::LeanObject,
    mut v_newNames_3170_: *mut leanh::LeanObject,
    mut v_tryToClear_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
    mut v_a_3176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryToClear_boxed_3177_: u8 = 0;
    let mut v_res_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryToClear_boxed_3177_ = (leanh::lean_unbox(v_tryToClear_3171_) as u8);
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
    leanh::lean_dec(v_a_3175_);
    leanh::lean_dec_ref(v_a_3174_);
    leanh::lean_dec(v_a_3173_);
    leanh::lean_dec_ref(v_a_3172_);
    return v_res_3178_;
}
pub unsafe fn l_Lean_Meta_injection(
    mut v_mvarId_3179_: *mut leanh::LeanObject,
    mut v_fvarId_3180_: *mut leanh::LeanObject,
    mut v_newNames_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
    mut v_a_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
    mut v_a_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numNewEqs_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_3187_) == 0 {
                    v_a_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                    v_isSharedCheck_3200_ = (!leanh::lean_is_exclusive(v___x_3187_)) as u8;
                    if v_isSharedCheck_3200_ == 0 {
                        v___x_3190_ = v___x_3187_;
                        v_isShared_3191_ = v_isSharedCheck_3200_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3188_);
                        leanh::lean_dec(v___x_3187_);
                        v___x_3190_ = leanh::lean_box(0);
                        v_isShared_3191_ = v_isSharedCheck_3200_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_newNames_3181_);
                    v_a_3201_ = leanh::lean_ctor_get(v___x_3187_, 0);
                    v_isSharedCheck_3208_ = (!leanh::lean_is_exclusive(v___x_3187_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3203_ = v___x_3187_;
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3201_);
                        leanh::lean_dec(v___x_3187_);
                        v___x_3203_ = leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3188_) == 0 {
                    leanh::lean_dec(v_newNames_3181_);
                    v___x_3192_ = leanh::lean_box(0);
                    if v_isShared_3191_ == 0 {
                        leanh::lean_ctor_set(v___x_3190_, 0, v___x_3192_);
                        v___x_3194_ = v___x_3190_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
                        v___x_3194_ = v_reuseFailAlloc_3195_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3190_);
                    v_mvarId_3196_ = leanh::lean_ctor_get(v_a_3188_, 0);
                    leanh::lean_inc(v_mvarId_3196_);
                    v_numNewEqs_3197_ = leanh::lean_ctor_get(v_a_3188_, 1);
                    leanh::lean_inc(v_numNewEqs_3197_);
                    leanh::lean_dec_ref_known(v_a_3188_, 2);
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
                    v_reuseFailAlloc_3207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
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
    mut v_mvarId_3209_: *mut leanh::LeanObject,
    mut v_fvarId_3210_: *mut leanh::LeanObject,
    mut v_newNames_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
    mut v_a_3213_: *mut leanh::LeanObject,
    mut v_a_3214_: *mut leanh::LeanObject,
    mut v_a_3215_: *mut leanh::LeanObject,
    mut v_a_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3217_ = l_Lean_Meta_injection(
        v_mvarId_3209_,
        v_fvarId_3210_,
        v_newNames_3211_,
        v_a_3212_,
        v_a_3213_,
        v_a_3214_,
        v_a_3215_,
    );
    leanh::lean_dec(v_a_3215_);
    leanh::lean_dec_ref(v_a_3214_);
    leanh::lean_dec(v_a_3213_);
    leanh::lean_dec_ref(v_a_3212_);
    return v_res_3217_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorIdx(
    mut v_x_3218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3218_) == 0 {
        let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3219_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3219_;
    } else {
        let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3220_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3220_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorIdx___boxed(
    mut v_x_3221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_Lean_Meta_InjectionsResult_ctorIdx(v_x_3221_);
    leanh::lean_dec(v_x_3221_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim___redArg(
    mut v_t_3223_: *mut leanh::LeanObject,
    mut v_k_3224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3223_) == 0 {
        return v_k_3224_;
    } else {
        let mut v_mvarId_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_remainingNames_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_forbidden_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarId_3225_ = leanh::lean_ctor_get(v_t_3223_, 0);
        leanh::lean_inc(v_mvarId_3225_);
        v_remainingNames_3226_ = leanh::lean_ctor_get(v_t_3223_, 1);
        leanh::lean_inc(v_remainingNames_3226_);
        v_forbidden_3227_ = leanh::lean_ctor_get(v_t_3223_, 2);
        leanh::lean_inc(v_forbidden_3227_);
        leanh::lean_dec_ref_known(v_t_3223_, 3);
        v___x_3228_ = leanh::lean_apply_3(
            v_k_3224_,
            v_mvarId_3225_,
            v_remainingNames_3226_,
            v_forbidden_3227_,
        );
        return v___x_3228_;
    }
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim(
    mut v_motive_3229_: *mut leanh::LeanObject,
    mut v_ctorIdx_3230_: *mut leanh::LeanObject,
    mut v_t_3231_: *mut leanh::LeanObject,
    mut v_h_3232_: *mut leanh::LeanObject,
    mut v_k_3233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3231_, v_k_3233_);
    return v___x_3234_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_ctorElim___boxed(
    mut v_motive_3235_: *mut leanh::LeanObject,
    mut v_ctorIdx_3236_: *mut leanh::LeanObject,
    mut v_t_3237_: *mut leanh::LeanObject,
    mut v_h_3238_: *mut leanh::LeanObject,
    mut v_k_3239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Meta_InjectionsResult_ctorElim(
        v_motive_3235_,
        v_ctorIdx_3236_,
        v_t_3237_,
        v_h_3238_,
        v_k_3239_,
    );
    leanh::lean_dec(v_ctorIdx_3236_);
    return v_res_3240_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_solved_elim___redArg(
    mut v_t_3241_: *mut leanh::LeanObject,
    mut v_solved_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3241_, v_solved_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_solved_elim(
    mut v_motive_3244_: *mut leanh::LeanObject,
    mut v_t_3245_: *mut leanh::LeanObject,
    mut v_h_3246_: *mut leanh::LeanObject,
    mut v_solved_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3245_, v_solved_3247_);
    return v___x_3248_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_subgoal_elim___redArg(
    mut v_t_3249_: *mut leanh::LeanObject,
    mut v_subgoal_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3249_, v_subgoal_3250_);
    return v___x_3251_;
}
pub unsafe fn l_Lean_Meta_InjectionsResult_subgoal_elim(
    mut v_motive_3252_: *mut leanh::LeanObject,
    mut v_t_3253_: *mut leanh::LeanObject,
    mut v_h_3254_: *mut leanh::LeanObject,
    mut v_subgoal_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Meta_InjectionsResult_ctorElim___redArg(v_t_3253_, v_subgoal_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(
    mut v_x_3257_: *mut leanh::LeanObject,
    mut v___y_3258_: *mut leanh::LeanObject,
    mut v___y_3259_: *mut leanh::LeanObject,
    mut v___y_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: u8 = 0;
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3272_: u8 = 0;
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3276_: u8 = 0;
    let mut v_unused_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: u8 = 0;
    let mut v_a_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3263_ = l_Lean_Meta_saveState___redArg(v___y_3259_, v___y_3261_);
                if leanh::lean_obj_tag(v___x_3263_) == 0 {
                    v_a_3264_ = leanh::lean_ctor_get(v___x_3263_, 0);
                    leanh::lean_inc(v_a_3264_);
                    leanh::lean_dec_ref_known(v___x_3263_, 1);
                    leanh::lean_inc(v___y_3261_);
                    leanh::lean_inc_ref(v___y_3260_);
                    leanh::lean_inc(v___y_3259_);
                    leanh::lean_inc_ref(v___y_3258_);
                    v___x_3265_ = leanh::lean_apply_5(
                        v_x_3257_,
                        v___y_3258_,
                        v___y_3259_,
                        v___y_3260_,
                        v___y_3261_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3265_) == 0 {
                        leanh::lean_dec(v_a_3264_);
                        return v___x_3265_;
                    } else {
                        v_a_3266_ = leanh::lean_ctor_get(v___x_3265_, 0);
                        leanh::lean_inc(v_a_3266_);
                        v___x_3286_ = l_Lean_Exception_isInterrupt(v_a_3266_);
                        if v___x_3286_ == 0 {
                            leanh::lean_inc(v_a_3266_);
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
                    leanh::lean_dec_ref(v_x_3257_);
                    v_a_3288_ = leanh::lean_ctor_get(v___x_3263_, 0);
                    v_isSharedCheck_3295_ = (!leanh::lean_is_exclusive(v___x_3263_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3263_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3288_);
                        leanh::lean_dec(v___x_3263_);
                        v___x_3290_ = leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3268_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3265_, 1);
                    v___x_3269_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_3264_,
                        v___y_3259_,
                        v___y_3261_,
                    );
                    leanh::lean_dec(v_a_3264_);
                    if leanh::lean_obj_tag(v___x_3269_) == 0 {
                        v_isSharedCheck_3276_ =
                            (!leanh::lean_is_exclusive(v___x_3269_)) as u8;
                        if v_isSharedCheck_3276_ == 0 {
                            v_unused_3277_ = leanh::lean_ctor_get(v___x_3269_, 0);
                            leanh::lean_dec(v_unused_3277_);
                            v___x_3271_ = v___x_3269_;
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3269_);
                            v___x_3271_ = leanh::lean_box(0);
                            v_isShared_3272_ = v_isSharedCheck_3276_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3266_);
                        v_a_3278_ = leanh::lean_ctor_get(v___x_3269_, 0);
                        v_isSharedCheck_3285_ =
                            (!leanh::lean_is_exclusive(v___x_3269_)) as u8;
                        if v_isSharedCheck_3285_ == 0 {
                            v___x_3280_ = v___x_3269_;
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3278_);
                            leanh::lean_dec(v___x_3269_);
                            v___x_3280_ = leanh::lean_box(0);
                            v_isShared_3281_ = v_isSharedCheck_3285_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3266_);
                    leanh::lean_dec(v_a_3264_);
                    return v___x_3265_;
                }
            }
            2 => {
                if v_isShared_3272_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3271_, 1);
                    leanh::lean_ctor_set(v___x_3271_, 0, v_a_3266_);
                    v___x_3274_ = v___x_3271_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3266_);
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
                    v_reuseFailAlloc_3284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
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
                    v_reuseFailAlloc_3294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
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
    mut v_x_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
    mut v___y_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3302_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    leanh::lean_dec(v___y_3300_);
    leanh::lean_dec_ref(v___y_3299_);
    leanh::lean_dec(v___y_3298_);
    leanh::lean_dec_ref(v___y_3297_);
    return v_res_3302_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(
    mut v_00_u03b1_3303_: *mut leanh::LeanObject,
    mut v_x_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
    return v___x_3310_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___boxed(
    mut v_00_u03b1_3311_: *mut leanh::LeanObject,
    mut v_x_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
    mut v___y_3315_: *mut leanh::LeanObject,
    mut v___y_3316_: *mut leanh::LeanObject,
    mut v___y_3317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3318_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1(v_00_u03b1_3311_, v_x_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
    leanh::lean_dec(v___y_3316_);
    leanh::lean_dec_ref(v___y_3315_);
    leanh::lean_dec(v___y_3314_);
    leanh::lean_dec_ref(v___y_3313_);
    return v_res_3318_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(
    mut v_k_3319_: *mut leanh::LeanObject,
    mut v_t_3320_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3326_: u8 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3320_) == 0 {
                    v_k_3321_ = leanh::lean_ctor_get(v_t_3320_, 1);
                    v_l_3322_ = leanh::lean_ctor_get(v_t_3320_, 3);
                    v_r_3323_ = leanh::lean_ctor_get(v_t_3320_, 4);
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
    mut v_k_3329_: *mut leanh::LeanObject,
    mut v_t_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3331_: u8 = 0;
    let mut v_r_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_3329_, v_t_3330_);
    leanh::lean_dec(v_t_3330_);
    leanh::lean_dec(v_k_3329_);
    v_r_3332_ = leanh::lean_box((v_res_3331_) as usize);
    return v_r_3332_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__3;
    v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
    return v___x_3340_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4_once
        ),
        _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__4,
    );
    v___x_3342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3342_, 0, v___x_3341_);
    return v___x_3342_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed(
    mut v_mvarId_3343_: *mut leanh::LeanObject,
    mut v_head_3344_: *mut leanh::LeanObject,
    mut v_newNames_3345_: *mut leanh::LeanObject,
    mut v_tail_3346_: *mut leanh::LeanObject,
    mut v_forbidden_3347_: *mut leanh::LeanObject,
    mut v_n_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v___y_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3352_);
    leanh::lean_dec_ref(v___y_3351_);
    leanh::lean_dec(v___y_3350_);
    leanh::lean_dec_ref(v___y_3349_);
    return v_res_3354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go(
    mut v_depth_3355_: *mut leanh::LeanObject,
    mut v_fvarIds_3356_: *mut leanh::LeanObject,
    mut v_mvarId_3357_: *mut leanh::LeanObject,
    mut v_newNames_3358_: *mut leanh::LeanObject,
    mut v_forbidden_3359_: *mut leanh::LeanObject,
    mut v_a_3360_: *mut leanh::LeanObject,
    mut v_a_3361_: *mut leanh::LeanObject,
    mut v_a_3362_: *mut leanh::LeanObject,
    mut v_a_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3366_: u8 = 0;
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: u8 = 0;
    let mut v___x_3381_: u8 = 0;
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: u8 = 0;
    let mut v_a_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3411_: u8 = 0;
    let mut v_a_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3419_: u8 = 0;
    let mut v_a_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v_a_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3432_: u8 = 0;
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3365_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3366_ = lean_nat_dec_eq(v_depth_3355_, v_zero_3365_);
                if v_isZero_3366_ == 1 {
                    leanh::lean_dec(v_forbidden_3359_);
                    leanh::lean_dec(v_newNames_3358_);
                    leanh::lean_dec(v_fvarIds_3356_);
                    leanh::lean_dec(v_depth_3355_);
                    v___x_3367_ = l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__1;
                    v___x_3368_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5_once), _init_l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___closed__5);
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
                    if leanh::lean_obj_tag(v_fvarIds_3356_) == 0 {
                        leanh::lean_dec(v_depth_3355_);
                        v___x_3370_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_3370_, 0, v_mvarId_3357_);
                        leanh::lean_ctor_set(v___x_3370_, 1, v_newNames_3358_);
                        leanh::lean_ctor_set(v___x_3370_, 2, v_forbidden_3359_);
                        v___x_3371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3371_, 0, v___x_3370_);
                        return v___x_3371_;
                    } else {
                        v_head_3372_ = leanh::lean_ctor_get(v_fvarIds_3356_, 0);
                        leanh::lean_inc(v_head_3372_);
                        v_tail_3373_ = leanh::lean_ctor_get(v_fvarIds_3356_, 1);
                        leanh::lean_inc(v_tail_3373_);
                        leanh::lean_dec_ref_known(v_fvarIds_3356_, 2);
                        v_one_3374_ = leanh::lean_unsigned_to_nat(1);
                        v_n_3375_ = lean_nat_sub(v_depth_3355_, v_one_3374_);
                        leanh::lean_dec(v_depth_3355_);
                        v___x_3376_ = lean_nat_add(v_n_3375_, v_one_3374_);
                        v___x_3381_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_head_3372_, v_forbidden_3359_);
                        if v___x_3381_ == 0 {
                            leanh::lean_inc(v_head_3372_);
                            v___x_3382_ = l_Lean_FVarId_getType___redArg(
                                v_head_3372_,
                                v_a_3360_,
                                v_a_3362_,
                                v_a_3363_,
                            );
                            if leanh::lean_obj_tag(v___x_3382_) == 0 {
                                v_a_3383_ = leanh::lean_ctor_get(v___x_3382_, 0);
                                leanh::lean_inc(v_a_3383_);
                                leanh::lean_dec_ref_known(v___x_3382_, 1);
                                v___x_3384_ = l_Lean_Meta_matchEqHEq_x3f(
                                    v_a_3383_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_,
                                );
                                if leanh::lean_obj_tag(v___x_3384_) == 0 {
                                    v_a_3385_ = leanh::lean_ctor_get(v___x_3384_, 0);
                                    leanh::lean_inc(v_a_3385_);
                                    leanh::lean_dec_ref_known(v___x_3384_, 1);
                                    if leanh::lean_obj_tag(v_a_3385_) == 1 {
                                        v_val_3386_ = leanh::lean_ctor_get(v_a_3385_, 0);
                                        leanh::lean_inc(v_val_3386_);
                                        leanh::lean_dec_ref_known(v_a_3385_, 1);
                                        v_snd_3387_ = leanh::lean_ctor_get(v_val_3386_, 1);
                                        leanh::lean_inc(v_snd_3387_);
                                        leanh::lean_dec(v_val_3386_);
                                        v_fst_3388_ = leanh::lean_ctor_get(v_snd_3387_, 0);
                                        leanh::lean_inc(v_fst_3388_);
                                        v_snd_3389_ = leanh::lean_ctor_get(v_snd_3387_, 1);
                                        leanh::lean_inc(v_snd_3389_);
                                        leanh::lean_dec(v_snd_3387_);
                                        leanh::lean_inc(v_a_3363_);
                                        leanh::lean_inc_ref(v_a_3362_);
                                        leanh::lean_inc(v_a_3361_);
                                        leanh::lean_inc_ref(v_a_3360_);
                                        v___x_3390_ = lean_whnf(
                                            v_fst_3388_,
                                            v_a_3360_,
                                            v_a_3361_,
                                            v_a_3362_,
                                            v_a_3363_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3390_) == 0 {
                                            v_a_3391_ = leanh::lean_ctor_get(v___x_3390_, 0);
                                            leanh::lean_inc(v_a_3391_);
                                            leanh::lean_dec_ref_known(v___x_3390_, 1);
                                            leanh::lean_inc(v_a_3363_);
                                            leanh::lean_inc_ref(v_a_3362_);
                                            leanh::lean_inc(v_a_3361_);
                                            leanh::lean_inc_ref(v_a_3360_);
                                            v___x_3392_ = lean_whnf(
                                                v_snd_3389_,
                                                v_a_3360_,
                                                v_a_3361_,
                                                v_a_3362_,
                                                v_a_3363_,
                                            );
                                            if leanh::lean_obj_tag(v___x_3392_) == 0 {
                                                v_a_3393_ =
                                                    leanh::lean_ctor_get(v___x_3392_, 0);
                                                leanh::lean_inc(v_a_3393_);
                                                leanh::lean_dec_ref_known(v___x_3392_, 1);
                                                leanh::lean_inc(v_forbidden_3359_);
                                                leanh::lean_inc(v_tail_3373_);
                                                leanh::lean_inc(v_newNames_3358_);
                                                leanh::lean_inc(v_mvarId_3357_);
                                                v___f_3394_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    0,
                                                    v_mvarId_3357_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    1,
                                                    v_head_3372_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    2,
                                                    v_newNames_3358_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    3,
                                                    v_tail_3373_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    4,
                                                    v_forbidden_3359_,
                                                );
                                                leanh::lean_closure_set(
                                                    v___f_3394_,
                                                    5,
                                                    v_n_3375_,
                                                );
                                                v___x_3402_ = l_Lean_Expr_isRawNatLit(v_a_3391_);
                                                leanh::lean_dec(v_a_3391_);
                                                if v___x_3402_ == 0 {
                                                    leanh::lean_dec(v_a_3393_);
                                                    v___y_3396_ = v___x_3402_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_3403_ =
                                                        l_Lean_Expr_isRawNatLit(v_a_3393_);
                                                    leanh::lean_dec(v_a_3393_);
                                                    v___y_3396_ = v___x_3403_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_3391_);
                                                leanh::lean_dec(v___x_3376_);
                                                leanh::lean_dec(v_n_3375_);
                                                leanh::lean_dec(v_tail_3373_);
                                                leanh::lean_dec(v_head_3372_);
                                                leanh::lean_dec(v_forbidden_3359_);
                                                leanh::lean_dec(v_newNames_3358_);
                                                leanh::lean_dec(v_mvarId_3357_);
                                                v_a_3404_ =
                                                    leanh::lean_ctor_get(v___x_3392_, 0);
                                                v_isSharedCheck_3411_ =
                                                    (!leanh::lean_is_exclusive(v___x_3392_))
                                                        as u8;
                                                if v_isSharedCheck_3411_ == 0 {
                                                    v___x_3406_ = v___x_3392_;
                                                    v_isShared_3407_ = v_isSharedCheck_3411_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_3404_);
                                                    leanh::lean_dec(v___x_3392_);
                                                    v___x_3406_ = leanh::lean_box(0);
                                                    v_isShared_3407_ = v_isSharedCheck_3411_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_snd_3389_);
                                            leanh::lean_dec(v___x_3376_);
                                            leanh::lean_dec(v_n_3375_);
                                            leanh::lean_dec(v_tail_3373_);
                                            leanh::lean_dec(v_head_3372_);
                                            leanh::lean_dec(v_forbidden_3359_);
                                            leanh::lean_dec(v_newNames_3358_);
                                            leanh::lean_dec(v_mvarId_3357_);
                                            v_a_3412_ = leanh::lean_ctor_get(v___x_3390_, 0);
                                            v_isSharedCheck_3419_ =
                                                (!leanh::lean_is_exclusive(v___x_3390_))
                                                    as u8;
                                            if v_isSharedCheck_3419_ == 0 {
                                                v___x_3414_ = v___x_3390_;
                                                v_isShared_3415_ = v_isSharedCheck_3419_;
                                                state = 5;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3412_);
                                                leanh::lean_dec(v___x_3390_);
                                                v___x_3414_ = leanh::lean_box(0);
                                                v_isShared_3415_ = v_isSharedCheck_3419_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3385_);
                                        leanh::lean_dec(v_n_3375_);
                                        leanh::lean_dec(v_head_3372_);
                                        v_depth_3355_ = v___x_3376_;
                                        v_fvarIds_3356_ = v_tail_3373_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_3376_);
                                    leanh::lean_dec(v_n_3375_);
                                    leanh::lean_dec(v_tail_3373_);
                                    leanh::lean_dec(v_head_3372_);
                                    leanh::lean_dec(v_forbidden_3359_);
                                    leanh::lean_dec(v_newNames_3358_);
                                    leanh::lean_dec(v_mvarId_3357_);
                                    v_a_3421_ = leanh::lean_ctor_get(v___x_3384_, 0);
                                    v_isSharedCheck_3428_ =
                                        (!leanh::lean_is_exclusive(v___x_3384_)) as u8;
                                    if v_isSharedCheck_3428_ == 0 {
                                        v___x_3423_ = v___x_3384_;
                                        v_isShared_3424_ = v_isSharedCheck_3428_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3421_);
                                        leanh::lean_dec(v___x_3384_);
                                        v___x_3423_ = leanh::lean_box(0);
                                        v_isShared_3424_ = v_isSharedCheck_3428_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_3376_);
                                leanh::lean_dec(v_n_3375_);
                                leanh::lean_dec(v_tail_3373_);
                                leanh::lean_dec(v_head_3372_);
                                leanh::lean_dec(v_forbidden_3359_);
                                leanh::lean_dec(v_newNames_3358_);
                                leanh::lean_dec(v_mvarId_3357_);
                                v_a_3429_ = leanh::lean_ctor_get(v___x_3382_, 0);
                                v_isSharedCheck_3436_ =
                                    (!leanh::lean_is_exclusive(v___x_3382_)) as u8;
                                if v_isSharedCheck_3436_ == 0 {
                                    v___x_3431_ = v___x_3382_;
                                    v_isShared_3432_ = v_isSharedCheck_3436_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3429_);
                                    leanh::lean_dec(v___x_3382_);
                                    v___x_3431_ = leanh::lean_box(0);
                                    v_isShared_3432_ = v_isSharedCheck_3436_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_n_3375_);
                            leanh::lean_dec(v_head_3372_);
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
                    leanh::lean_dec_ref(v___y_3378_);
                    v_depth_3355_ = v___x_3376_;
                    v_fvarIds_3356_ = v_tail_3373_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3376_);
                    leanh::lean_dec(v_tail_3373_);
                    leanh::lean_dec(v_forbidden_3359_);
                    leanh::lean_dec(v_newNames_3358_);
                    leanh::lean_dec(v_mvarId_3357_);
                    return v___y_3378_;
                }
            }
            2 => {
                if v___y_3396_ == 0 {
                    v___x_3397_ = l_Lean_commitIfNoEx___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__1___redArg(v___f_3394_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
                    if leanh::lean_obj_tag(v___x_3397_) == 0 {
                        leanh::lean_dec(v___x_3376_);
                        leanh::lean_dec(v_tail_3373_);
                        leanh::lean_dec(v_forbidden_3359_);
                        leanh::lean_dec(v_newNames_3358_);
                        leanh::lean_dec(v_mvarId_3357_);
                        return v___x_3397_;
                    } else {
                        v_a_3398_ = leanh::lean_ctor_get(v___x_3397_, 0);
                        leanh::lean_inc(v_a_3398_);
                        v___x_3399_ = l_Lean_Exception_isInterrupt(v_a_3398_);
                        if v___x_3399_ == 0 {
                            v___x_3400_ = l_Lean_Exception_isRuntime(v_a_3398_);
                            v___y_3378_ = v___x_3397_;
                            v___y_3379_ = v___x_3400_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3398_);
                            v___y_3378_ = v___x_3397_;
                            v___y_3379_ = v___x_3399_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_3394_);
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
                    v_reuseFailAlloc_3410_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
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
                    v_reuseFailAlloc_3418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
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
                    v_reuseFailAlloc_3427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
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
                    v_reuseFailAlloc_3435_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
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
    mut v_depth_3438_: *mut leanh::LeanObject,
    mut v_fvarIds_3439_: *mut leanh::LeanObject,
    mut v_mvarId_3440_: *mut leanh::LeanObject,
    mut v_newNames_3441_: *mut leanh::LeanObject,
    mut v_forbidden_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3446_);
    leanh::lean_dec_ref(v_a_3445_);
    leanh::lean_dec(v_a_3444_);
    leanh::lean_dec_ref(v_a_3443_);
    return v_res_3448_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___lam__0(
    mut v_mvarId_3449_: *mut leanh::LeanObject,
    mut v_head_3450_: *mut leanh::LeanObject,
    mut v_newNames_3451_: *mut leanh::LeanObject,
    mut v_tail_3452_: *mut leanh::LeanObject,
    mut v_forbidden_3453_: *mut leanh::LeanObject,
    mut v_n_3454_: *mut leanh::LeanObject,
    mut v___y_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEqs_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_a_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_head_3450_);
                v___x_3460_ = l_Lean_Meta_injection(
                    v_mvarId_3449_,
                    v_head_3450_,
                    v_newNames_3451_,
                    v___y_3455_,
                    v___y_3456_,
                    v___y_3457_,
                    v___y_3458_,
                );
                if leanh::lean_obj_tag(v___x_3460_) == 0 {
                    v_a_3461_ = leanh::lean_ctor_get(v___x_3460_, 0);
                    v_isSharedCheck_3477_ = (!leanh::lean_is_exclusive(v___x_3460_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3463_ = v___x_3460_;
                        v_isShared_3464_ = v_isSharedCheck_3477_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3461_);
                        leanh::lean_dec(v___x_3460_);
                        v___x_3463_ = leanh::lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3477_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_n_3454_);
                    leanh::lean_dec(v_forbidden_3453_);
                    leanh::lean_dec(v_tail_3452_);
                    leanh::lean_dec(v_head_3450_);
                    v_a_3478_ = leanh::lean_ctor_get(v___x_3460_, 0);
                    v_isSharedCheck_3485_ = (!leanh::lean_is_exclusive(v___x_3460_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v___x_3480_ = v___x_3460_;
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3478_);
                        leanh::lean_dec(v___x_3460_);
                        v___x_3480_ = leanh::lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3485_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3461_) == 0 {
                    leanh::lean_dec(v_n_3454_);
                    leanh::lean_dec(v_forbidden_3453_);
                    leanh::lean_dec(v_tail_3452_);
                    leanh::lean_dec(v_head_3450_);
                    v___x_3465_ = leanh::lean_box(0);
                    if v_isShared_3464_ == 0 {
                        leanh::lean_ctor_set(v___x_3463_, 0, v___x_3465_);
                        v___x_3467_ = v___x_3463_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3463_);
                    v_mvarId_3469_ = leanh::lean_ctor_get(v_a_3461_, 0);
                    leanh::lean_inc_n(v_mvarId_3469_, 2);
                    v_newEqs_3470_ = leanh::lean_ctor_get(v_a_3461_, 1);
                    leanh::lean_inc_ref(v_newEqs_3470_);
                    v_remainingNames_3471_ = leanh::lean_ctor_get(v_a_3461_, 2);
                    leanh::lean_inc(v_remainingNames_3471_);
                    leanh::lean_dec_ref_known(v_a_3461_, 3);
                    v___x_3472_ = lean_array_to_list(v_newEqs_3470_);
                    v___x_3473_ = l_List_appendTR___redArg(v___x_3472_, v_tail_3452_);
                    v___x_3474_ = l_Lean_FVarIdSet_insert(v_forbidden_3453_, v_head_3450_);
                    v___x_3475_ = leanh::lean_alloc_closure(
                        l___private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    leanh::lean_closure_set(v___x_3475_, 0, v_n_3454_);
                    leanh::lean_closure_set(v___x_3475_, 1, v___x_3473_);
                    leanh::lean_closure_set(v___x_3475_, 2, v_mvarId_3469_);
                    leanh::lean_closure_set(v___x_3475_, 3, v_remainingNames_3471_);
                    leanh::lean_closure_set(v___x_3475_, 4, v___x_3474_);
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
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
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
    mut v_00_u03b2_3486_: *mut leanh::LeanObject,
    mut v_k_3487_: *mut leanh::LeanObject,
    mut v_t_3488_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3489_: u8 = 0;
    v___x_3489_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___redArg(v_k_3487_, v_t_3488_);
    return v___x_3489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0___boxed(
    mut v_00_u03b2_3490_: *mut leanh::LeanObject,
    mut v_k_3491_: *mut leanh::LeanObject,
    mut v_t_3492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3493_: u8 = 0;
    let mut v_r_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Injection_0__Lean_Meta_injections_go_spec__0(v_00_u03b2_3490_, v_k_3491_, v_t_3492_);
    leanh::lean_dec(v_t_3492_);
    leanh::lean_dec(v_k_3491_);
    v_r_3494_ = leanh::lean_box((v_res_3493_) as usize);
    return v_r_3494_;
}
pub unsafe fn l_Lean_Meta_injections___lam__0(
    mut v_maxDepth_3495_: *mut leanh::LeanObject,
    mut v_mvarId_3496_: *mut leanh::LeanObject,
    mut v_newNames_3497_: *mut leanh::LeanObject,
    mut v_forbidden_3498_: *mut leanh::LeanObject,
    mut v___y_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3504_ = leanh::lean_ctor_get(v___y_3499_, 2);
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
    mut v_maxDepth_3508_: *mut leanh::LeanObject,
    mut v_mvarId_3509_: *mut leanh::LeanObject,
    mut v_newNames_3510_: *mut leanh::LeanObject,
    mut v_forbidden_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3515_);
    leanh::lean_dec_ref(v___y_3514_);
    leanh::lean_dec(v___y_3513_);
    leanh::lean_dec_ref(v___y_3512_);
    return v_res_3517_;
}
pub unsafe fn l_Lean_Meta_injections(
    mut v_mvarId_3518_: *mut leanh::LeanObject,
    mut v_newNames_3519_: *mut leanh::LeanObject,
    mut v_maxDepth_3520_: *mut leanh::LeanObject,
    mut v_forbidden_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
    mut v_a_3523_: *mut leanh::LeanObject,
    mut v_a_3524_: *mut leanh::LeanObject,
    mut v_a_3525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_3518_);
    v___f_3527_ = leanh::lean_alloc_closure(
        l_Lean_Meta_injections___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_3527_, 0, v_maxDepth_3520_);
    leanh::lean_closure_set(v___f_3527_, 1, v_mvarId_3518_);
    leanh::lean_closure_set(v___f_3527_, 2, v_newNames_3519_);
    leanh::lean_closure_set(v___f_3527_, 3, v_forbidden_3521_);
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
    mut v_mvarId_3529_: *mut leanh::LeanObject,
    mut v_newNames_3530_: *mut leanh::LeanObject,
    mut v_maxDepth_3531_: *mut leanh::LeanObject,
    mut v_forbidden_3532_: *mut leanh::LeanObject,
    mut v_a_3533_: *mut leanh::LeanObject,
    mut v_a_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_3536_);
    leanh::lean_dec_ref(v_a_3535_);
    leanh::lean_dec(v_a_3534_);
    leanh::lean_dec_ref(v_a_3533_);
    return v_res_3538_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: u8 = 0;
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_Meta_injectionIntro___closed__1;
    v___x_3596_ = 0;
    v___x_3597_ = l___private_Lean_Meta_Tactic_Injection_0__initFn___closed__22_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_;
    v___x_3598_ = l_Lean_registerTraceClass(v___x_3595_, v___x_3596_, v___x_3597_);
    return v___x_3598_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2____boxed(
    mut v_a_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
    return v_res_3600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Injection(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Injection_0__initFn_00___x40_Lean_Meta_Tactic_Injection_1583609249____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Injection(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Injection(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Subst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Injection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Injection(builtin);
}