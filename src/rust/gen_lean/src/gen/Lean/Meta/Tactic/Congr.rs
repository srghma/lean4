// Lean compiler output
// Module: Lean.Meta.Tactic.Congr
// Imports: Lean.Meta.CongrTheorems Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Assumption
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_nat_dec_eq, lean_nat_sub, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_instBEqTransparencyMode_beq;
use crate::r#gen::Lean::CoreM::{l_Lean_Core_mkFreshUserName, l_Lean_Exception_isRuntime};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity,
    l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_mkConstWithFreshMVarLevels,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::CongrTheorems::{
    initialize_Lean_Meta_CongrTheorems, l_Lean_Meta_mkCongrSimp_x3f, l_Lean_Meta_mkHCongrWithArity,
    runtime_initialize_Lean_Meta_CongrTheorems,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::l_Lean_MVarId_apply;
use crate::r#gen::Lean::Meta::Tactic::Assert::{
    initialize_Lean_Meta_Tactic_Assert, l_Lean_MVarId_assert,
    runtime_initialize_Lean_Meta_Tactic_Assert,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_MVarId_assumptionCore,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_eqOfHEq, l_Lean_MVarId_heqOfEq,
    l_Lean_MVarId_hrefl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType_x27, l_Lean_Meta_throwTacticEx___redArg,
};
pub static l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 95, 99, 111, 110, 103, 114, 95, 116, 104, 109, 0],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15603447039181438785 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777216 as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Lean_MVarId_congr_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congr_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_MVarId_congr_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11699215918282396216 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congr_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_MVarId_hcongr_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13589827700912665667 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_hcongr_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777472 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<61> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 61,
    m_capacity: 61,
    m_length: 60,
    m_data: [
        73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 69, 120, 112,
        101, 99, 116, 101, 100, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 116, 119, 111, 32,
        103, 111, 97, 108, 115, 32, 97, 102, 116, 101, 114, 32, 97, 112, 112, 108, 121, 105, 110,
        103, 32, 96, 0,
    ],
};
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
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
        96, 44, 32, 98, 117, 116, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 108, 121,
        32, 102, 111, 117, 110, 100, 32, 102, 101, 119, 101, 114, 0,
    ],
};
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_congrImplies_x3f___closed__0_value: crate::leanh::LeanStringObject<14> =
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
            105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_MVarId_congrImplies_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11074994739801900941 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congrImplies_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congrCore___closed__0_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
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
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 99, 111, 110,
            103, 114, 117, 101, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_MVarId_congrCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_congrCore___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congrCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_congrCore___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_congrCore___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0: u64 = 0;
pub static l_Lean_MVarId_congrN___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_MVarId_congrN___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrN___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_congrPre(
    mut v_mvarId_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_a_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
    mut v_a_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___y_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: u8 = 0;
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v_a_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_unused_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___y_1232_: u8 = 0;
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v_unused_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_a_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1256_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1182_ = l_Lean_MVarId_heqOfEq(
                    v_mvarId_1176_,
                    v_a_1177_,
                    v_a_1178_,
                    v_a_1179_,
                    v_a_1180_,
                );
                if crate::leanh::lean_obj_tag(v___x_1182_) == 0 {
                    v_a_1183_ = crate::leanh::lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1252_ = (!crate::leanh::lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1252_ == 0 {
                        v___x_1185_ = v___x_1182_;
                        v_isShared_1186_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1183_);
                        crate::leanh::lean_dec(v___x_1182_);
                        v___x_1185_ = crate::leanh::lean_box(0);
                        v_isShared_1186_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1253_ = crate::leanh::lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1260_ = (!crate::leanh::lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1260_ == 0 {
                        v___x_1255_ = v___x_1182_;
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1253_);
                        crate::leanh::lean_dec(v___x_1182_);
                        v___x_1255_ = crate::leanh::lean_box(0);
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1216_ = 1;
                crate::leanh::lean_inc(v_a_1183_);
                v___x_1217_ = l_Lean_MVarId_refl(
                    v_a_1183_,
                    v___x_1216_,
                    v_a_1177_,
                    v_a_1178_,
                    v_a_1179_,
                    v_a_1180_,
                );
                if crate::leanh::lean_obj_tag(v___x_1217_) == 0 {
                    crate::leanh::lean_del_object(v___x_1185_);
                    crate::leanh::lean_dec(v_a_1183_);
                    v_isSharedCheck_1225_ = (!crate::leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v_unused_1226_ = crate::leanh::lean_ctor_get(v___x_1217_, 0);
                        crate::leanh::lean_dec(v_unused_1226_);
                        v___x_1219_ = v___x_1217_;
                        v_isShared_1220_ = v_isSharedCheck_1225_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1217_);
                        v___x_1219_ = crate::leanh::lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1225_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_1227_ = crate::leanh::lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1251_ = (!crate::leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1229_ = v___x_1217_;
                        v_isShared_1230_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1227_);
                        crate::leanh::lean_dec(v___x_1217_);
                        v___x_1229_ = crate::leanh::lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_1189_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_1188_);
                    crate::leanh::lean_del_object(v___x_1185_);
                    crate::leanh::lean_inc(v_a_1183_);
                    v___x_1190_ = l_Lean_MVarId_assumptionCore(
                        v_a_1183_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1190_) == 0 {
                        v_a_1191_ = crate::leanh::lean_ctor_get(v___x_1190_, 0);
                        v_isSharedCheck_1204_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1190_)) as u8;
                        if v_isSharedCheck_1204_ == 0 {
                            v___x_1193_ = v___x_1190_;
                            v_isShared_1194_ = v_isSharedCheck_1204_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1191_);
                            crate::leanh::lean_dec(v___x_1190_);
                            v___x_1193_ = crate::leanh::lean_box(0);
                            v_isShared_1194_ = v_isSharedCheck_1204_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1183_);
                        v_a_1205_ = crate::leanh::lean_ctor_get(v___x_1190_, 0);
                        v_isSharedCheck_1212_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1190_)) as u8;
                        if v_isSharedCheck_1212_ == 0 {
                            v___x_1207_ = v___x_1190_;
                            v_isShared_1208_ = v_isSharedCheck_1212_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1205_);
                            crate::leanh::lean_dec(v___x_1190_);
                            v___x_1207_ = crate::leanh::lean_box(0);
                            v_isShared_1208_ = v_isSharedCheck_1212_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1183_);
                    if v_isShared_1186_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1185_, 1);
                        crate::leanh::lean_ctor_set(v___x_1185_, 0, v___y_1188_);
                        v___x_1214_ = v___x_1185_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___y_1188_);
                        v___x_1214_ = v_reuseFailAlloc_1215_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1195_ = (crate::leanh::lean_unbox(v_a_1191_) as u8);
                crate::leanh::lean_dec(v_a_1191_);
                if v___x_1195_ == 0 {
                    v___x_1196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1196_, 0, v_a_1183_);
                    if v_isShared_1194_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1193_, 0, v___x_1196_);
                        v___x_1198_ = v___x_1193_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
                        v___x_1198_ = v_reuseFailAlloc_1199_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1183_);
                    v___x_1200_ = crate::leanh::lean_box(0);
                    if v_isShared_1194_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1193_, 0, v___x_1200_);
                        v___x_1202_ = v___x_1193_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
                        v___x_1202_ = v_reuseFailAlloc_1203_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1198_;
            }
            5 => {
                return v___x_1202_;
            }
            6 => {
                if v_isShared_1208_ == 0 {
                    v___x_1210_ = v___x_1207_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
                    v___x_1210_ = v_reuseFailAlloc_1211_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1210_;
            }
            8 => {
                return v___x_1214_;
            }
            9 => {
                v___x_1221_ = crate::leanh::lean_box(0);
                if v_isShared_1220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1219_, 0, v___x_1221_);
                    v___x_1223_ = v___x_1219_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1223_;
            }
            11 => {
                v___x_1249_ = l_Lean_Exception_isInterrupt(v_a_1227_);
                if v___x_1249_ == 0 {
                    crate::leanh::lean_inc(v_a_1227_);
                    v___x_1250_ = l_Lean_Exception_isRuntime(v_a_1227_);
                    v___y_1232_ = v___x_1250_;
                    state = 12;
                    continue;
                } else {
                    v___y_1232_ = v___x_1249_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v___y_1232_ == 0 {
                    crate::leanh::lean_del_object(v___x_1229_);
                    crate::leanh::lean_dec(v_a_1227_);
                    crate::leanh::lean_inc(v_a_1183_);
                    v___x_1233_ =
                        l_Lean_MVarId_hrefl(v_a_1183_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
                    if crate::leanh::lean_obj_tag(v___x_1233_) == 0 {
                        crate::leanh::lean_del_object(v___x_1185_);
                        crate::leanh::lean_dec(v_a_1183_);
                        v_isSharedCheck_1241_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1233_)) as u8;
                        if v_isSharedCheck_1241_ == 0 {
                            v_unused_1242_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                            crate::leanh::lean_dec(v_unused_1242_);
                            v___x_1235_ = v___x_1233_;
                            v_isShared_1236_ = v_isSharedCheck_1241_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1233_);
                            v___x_1235_ = crate::leanh::lean_box(0);
                            v_isShared_1236_ = v_isSharedCheck_1241_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_1243_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
                        crate::leanh::lean_inc(v_a_1243_);
                        crate::leanh::lean_dec_ref_known(v___x_1233_, 1);
                        v___x_1244_ = l_Lean_Exception_isInterrupt(v_a_1243_);
                        if v___x_1244_ == 0 {
                            crate::leanh::lean_inc(v_a_1243_);
                            v___x_1245_ = l_Lean_Exception_isRuntime(v_a_1243_);
                            v___y_1188_ = v_a_1243_;
                            v___y_1189_ = v___x_1245_;
                            state = 2;
                            continue;
                        } else {
                            v___y_1188_ = v_a_1243_;
                            v___y_1189_ = v___x_1244_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1185_);
                    crate::leanh::lean_dec(v_a_1183_);
                    if v_isShared_1230_ == 0 {
                        v___x_1247_ = v___x_1229_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1227_);
                        v___x_1247_ = v_reuseFailAlloc_1248_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1237_ = crate::leanh::lean_box(0);
                if v_isShared_1236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1235_, 0, v___x_1237_);
                    v___x_1239_ = v___x_1235_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1239_;
            }
            15 => {
                return v___x_1247_;
            }
            16 => {
                if v_isShared_1256_ == 0 {
                    v___x_1258_ = v___x_1255_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
                    v___x_1258_ = v_reuseFailAlloc_1259_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_congrPre___boxed(
    mut v_mvarId_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
    mut v_a_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ =
        l_Lean_MVarId_congrPre(v_mvarId_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
    crate::leanh::lean_dec(v_a_1265_);
    crate::leanh::lean_dec_ref(v_a_1264_);
    crate::leanh::lean_dec(v_a_1263_);
    crate::leanh::lean_dec_ref(v_a_1262_);
    return v_res_1267_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(
    mut v_fst_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
    mut v_x_1270_: *mut crate::leanh::LeanObject,
    mut v___y_1271_: *mut crate::leanh::LeanObject,
    mut v___y_1272_: *mut crate::leanh::LeanObject,
    mut v___y_1273_: *mut crate::leanh::LeanObject,
    mut v___y_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1269_) == 0 {
                    crate::leanh::lean_dec(v_fst_1268_);
                    v___x_1276_ = l_List_reverse___redArg(v_x_1270_);
                    v___x_1277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1276_);
                    return v___x_1277_;
                } else {
                    v_head_1278_ = crate::leanh::lean_ctor_get(v_x_1269_, 0);
                    v_tail_1279_ = crate::leanh::lean_ctor_get(v_x_1269_, 1);
                    v_isSharedCheck_1297_ = (!crate::leanh::lean_is_exclusive(v_x_1269_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v___x_1281_ = v_x_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1279_);
                        crate::leanh::lean_inc(v_head_1278_);
                        crate::leanh::lean_dec(v_x_1269_);
                        v___x_1281_ = crate::leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_fst_1268_);
                v___x_1283_ = l_Lean_MVarId_tryClear(
                    v_head_1278_,
                    v_fst_1268_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                );
                if crate::leanh::lean_obj_tag(v___x_1283_) == 0 {
                    v_a_1284_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                    crate::leanh::lean_inc(v_a_1284_);
                    crate::leanh::lean_dec_ref_known(v___x_1283_, 1);
                    if v_isShared_1282_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1281_, 1, v_x_1270_);
                        crate::leanh::lean_ctor_set(v___x_1281_, 0, v_a_1284_);
                        v___x_1286_ = v___x_1281_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1288_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1284_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_x_1270_);
                        v___x_1286_ = v_reuseFailAlloc_1288_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1281_);
                    crate::leanh::lean_dec(v_tail_1279_);
                    crate::leanh::lean_dec(v_x_1270_);
                    crate::leanh::lean_dec(v_fst_1268_);
                    v_a_1289_ = crate::leanh::lean_ctor_get(v___x_1283_, 0);
                    v_isSharedCheck_1296_ = (!crate::leanh::lean_is_exclusive(v___x_1283_)) as u8;
                    if v_isSharedCheck_1296_ == 0 {
                        v___x_1291_ = v___x_1283_;
                        v_isShared_1292_ = v_isSharedCheck_1296_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1289_);
                        crate::leanh::lean_dec(v___x_1283_);
                        v___x_1291_ = crate::leanh::lean_box(0);
                        v_isShared_1292_ = v_isSharedCheck_1296_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_1269_ = v_tail_1279_;
                v_x_1270_ = v___x_1286_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1292_ == 0 {
                    v___x_1294_ = v___x_1291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1295_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
                    v___x_1294_ = v_reuseFailAlloc_1295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0___boxed(
    mut v_fst_1298_: *mut crate::leanh::LeanObject,
    mut v_x_1299_: *mut crate::leanh::LeanObject,
    mut v_x_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_1298_, v_x_1299_, v_x_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
    crate::leanh::lean_dec(v___y_1304_);
    crate::leanh::lean_dec_ref(v___y_1303_);
    crate::leanh::lean_dec(v___y_1302_);
    crate::leanh::lean_dec_ref(v___y_1301_);
    return v_res_1306_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
    mut v_mvarId_1314_: *mut crate::leanh::LeanObject,
    mut v_congrThm_1315_: *mut crate::leanh::LeanObject,
    mut v_a_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
    mut v_a_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1347_: u8 = 0;
    let mut v_a_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_a_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ =
                    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1;
                v___x_1322_ = l_Lean_Core_mkFreshUserName(v___x_1321_, v_a_1318_, v_a_1319_);
                if crate::leanh::lean_obj_tag(v___x_1322_) == 0 {
                    v_a_1323_ = crate::leanh::lean_ctor_get(v___x_1322_, 0);
                    crate::leanh::lean_inc(v_a_1323_);
                    crate::leanh::lean_dec_ref_known(v___x_1322_, 1);
                    v_type_1324_ = crate::leanh::lean_ctor_get(v_congrThm_1315_, 0);
                    crate::leanh::lean_inc_ref(v_type_1324_);
                    v_proof_1325_ = crate::leanh::lean_ctor_get(v_congrThm_1315_, 1);
                    crate::leanh::lean_inc_ref(v_proof_1325_);
                    crate::leanh::lean_dec_ref(v_congrThm_1315_);
                    v___x_1326_ = l_Lean_MVarId_assert(
                        v_mvarId_1314_,
                        v_a_1323_,
                        v_type_1324_,
                        v_proof_1325_,
                        v_a_1316_,
                        v_a_1317_,
                        v_a_1318_,
                        v_a_1319_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1326_) == 0 {
                        v_a_1327_ = crate::leanh::lean_ctor_get(v___x_1326_, 0);
                        crate::leanh::lean_inc(v_a_1327_);
                        crate::leanh::lean_dec_ref_known(v___x_1326_, 1);
                        v___x_1328_ = 1;
                        v___x_1329_ = l_Lean_Meta_intro1Core(
                            v_a_1327_,
                            v___x_1328_,
                            v_a_1316_,
                            v_a_1317_,
                            v_a_1318_,
                            v_a_1319_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1329_) == 0 {
                            v_a_1330_ = crate::leanh::lean_ctor_get(v___x_1329_, 0);
                            crate::leanh::lean_inc(v_a_1330_);
                            crate::leanh::lean_dec_ref_known(v___x_1329_, 1);
                            v_fst_1331_ = crate::leanh::lean_ctor_get(v_a_1330_, 0);
                            crate::leanh::lean_inc_n(v_fst_1331_, 2);
                            v_snd_1332_ = crate::leanh::lean_ctor_get(v_a_1330_, 1);
                            crate::leanh::lean_inc(v_snd_1332_);
                            crate::leanh::lean_dec(v_a_1330_);
                            v___x_1333_ = l_Lean_mkFVar(v_fst_1331_);
                            v___x_1334_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2;
                            v___x_1335_ = crate::leanh::lean_box(0);
                            v___x_1336_ = l_Lean_MVarId_apply(
                                v_snd_1332_,
                                v___x_1333_,
                                v___x_1334_,
                                v___x_1335_,
                                v_a_1316_,
                                v_a_1317_,
                                v_a_1318_,
                                v_a_1319_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1336_) == 0 {
                                v_a_1337_ = crate::leanh::lean_ctor_get(v___x_1336_, 0);
                                crate::leanh::lean_inc(v_a_1337_);
                                crate::leanh::lean_dec_ref_known(v___x_1336_, 1);
                                v___x_1338_ = crate::leanh::lean_box(0);
                                v___x_1339_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_1331_, v_a_1337_, v___x_1338_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
                                return v___x_1339_;
                            } else {
                                crate::leanh::lean_dec(v_fst_1331_);
                                return v___x_1336_;
                            }
                        } else {
                            v_a_1340_ = crate::leanh::lean_ctor_get(v___x_1329_, 0);
                            v_isSharedCheck_1347_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1347_ == 0 {
                                v___x_1342_ = v___x_1329_;
                                v_isShared_1343_ = v_isSharedCheck_1347_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1340_);
                                crate::leanh::lean_dec(v___x_1329_);
                                v___x_1342_ = crate::leanh::lean_box(0);
                                v_isShared_1343_ = v_isSharedCheck_1347_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1348_ = crate::leanh::lean_ctor_get(v___x_1326_, 0);
                        v_isSharedCheck_1355_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1326_)) as u8;
                        if v_isSharedCheck_1355_ == 0 {
                            v___x_1350_ = v___x_1326_;
                            v_isShared_1351_ = v_isSharedCheck_1355_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1348_);
                            crate::leanh::lean_dec(v___x_1326_);
                            v___x_1350_ = crate::leanh::lean_box(0);
                            v_isShared_1351_ = v_isSharedCheck_1355_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_congrThm_1315_);
                    crate::leanh::lean_dec(v_mvarId_1314_);
                    v_a_1356_ = crate::leanh::lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1363_ = (!crate::leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1358_ = v___x_1322_;
                        v_isShared_1359_ = v_isSharedCheck_1363_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1356_);
                        crate::leanh::lean_dec(v___x_1322_);
                        v___x_1358_ = crate::leanh::lean_box(0);
                        v_isShared_1359_ = v_isSharedCheck_1363_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1343_ == 0 {
                    v___x_1345_ = v___x_1342_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
                    v___x_1345_ = v_reuseFailAlloc_1346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1345_;
            }
            3 => {
                if v_isShared_1351_ == 0 {
                    v___x_1353_ = v___x_1350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
                    v___x_1353_ = v_reuseFailAlloc_1354_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1353_;
            }
            5 => {
                if v_isShared_1359_ == 0 {
                    v___x_1361_ = v___x_1358_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___boxed(
    mut v_mvarId_1364_: *mut crate::leanh::LeanObject,
    mut v_congrThm_1365_: *mut crate::leanh::LeanObject,
    mut v_a_1366_: *mut crate::leanh::LeanObject,
    mut v_a_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_a_1369_: *mut crate::leanh::LeanObject,
    mut v_a_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1371_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
        v_mvarId_1364_,
        v_congrThm_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
    );
    crate::leanh::lean_dec(v_a_1369_);
    crate::leanh::lean_dec_ref(v_a_1368_);
    crate::leanh::lean_dec(v_a_1367_);
    crate::leanh::lean_dec_ref(v_a_1366_);
    return v_res_1371_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
    mut v_mvarId_1372_: *mut crate::leanh::LeanObject,
    mut v_x_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1372_,
                    v_x_1373_,
                    v___y_1374_,
                    v___y_1375_,
                    v___y_1376_,
                    v___y_1377_,
                );
                if crate::leanh::lean_obj_tag(v___x_1379_) == 0 {
                    v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                    v_isSharedCheck_1387_ = (!crate::leanh::lean_is_exclusive(v___x_1379_)) as u8;
                    if v_isSharedCheck_1387_ == 0 {
                        v___x_1382_ = v___x_1379_;
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1380_);
                        crate::leanh::lean_dec(v___x_1379_);
                        v___x_1382_ = crate::leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1388_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                    v_isSharedCheck_1395_ = (!crate::leanh::lean_is_exclusive(v___x_1379_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v___x_1390_ = v___x_1379_;
                        v_isShared_1391_ = v_isSharedCheck_1395_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1388_);
                        crate::leanh::lean_dec(v___x_1379_);
                        v___x_1390_ = crate::leanh::lean_box(0);
                        v_isShared_1391_ = v_isSharedCheck_1395_;
                        state = 3;
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
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
                    v___x_1385_ = v_reuseFailAlloc_1386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1385_;
            }
            3 => {
                if v_isShared_1391_ == 0 {
                    v___x_1393_ = v___x_1390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
                    v___x_1393_ = v_reuseFailAlloc_1394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg___boxed(
    mut v_mvarId_1396_: *mut crate::leanh::LeanObject,
    mut v_x_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
        v_mvarId_1396_,
        v_x_1397_,
        v___y_1398_,
        v___y_1399_,
        v___y_1400_,
        v___y_1401_,
    );
    crate::leanh::lean_dec(v___y_1401_);
    crate::leanh::lean_dec_ref(v___y_1400_);
    crate::leanh::lean_dec(v___y_1399_);
    crate::leanh::lean_dec_ref(v___y_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(
    mut v_00_u03b1_1404_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1405_: *mut crate::leanh::LeanObject,
    mut v_x_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1412_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
        v_mvarId_1405_,
        v_x_1406_,
        v___y_1407_,
        v___y_1408_,
        v___y_1409_,
        v___y_1410_,
    );
    return v___x_1412_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___boxed(
    mut v_00_u03b1_1413_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1414_: *mut crate::leanh::LeanObject,
    mut v_x_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(
        v_00_u03b1_1413_,
        v_mvarId_1414_,
        v_x_1415_,
        v___y_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
    );
    crate::leanh::lean_dec(v___y_1419_);
    crate::leanh::lean_dec_ref(v___y_1418_);
    crate::leanh::lean_dec(v___y_1417_);
    crate::leanh::lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_Lean_MVarId_congr_x3f___lam__0(
    mut v_mvarId_1425_: *mut crate::leanh::LeanObject,
    mut v___x_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u8 = 0;
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v_val_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_a_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_a_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v_a_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1425_);
                v___x_1432_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1425_,
                    v___x_1426_,
                    v___y_1427_,
                    v___y_1428_,
                    v___y_1429_,
                    v___y_1430_,
                );
                if crate::leanh::lean_obj_tag(v___x_1432_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1432_, 1);
                    crate::leanh::lean_inc(v_mvarId_1425_);
                    v___x_1433_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_1425_,
                        v___y_1427_,
                        v___y_1428_,
                        v___y_1429_,
                        v___y_1430_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1433_) == 0 {
                        v_a_1434_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                        v_isSharedCheck_1500_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1433_)) as u8;
                        if v_isSharedCheck_1500_ == 0 {
                            v___x_1436_ = v___x_1433_;
                            v_isShared_1437_ = v_isSharedCheck_1500_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1434_);
                            crate::leanh::lean_dec(v___x_1433_);
                            v___x_1436_ = crate::leanh::lean_box(0);
                            v_isShared_1437_ = v_isSharedCheck_1500_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_1425_);
                        v_a_1501_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                        v_isSharedCheck_1508_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1433_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1503_ = v___x_1433_;
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1501_);
                            crate::leanh::lean_dec(v___x_1433_);
                            v___x_1503_ = crate::leanh::lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1425_);
                    v_a_1509_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1516_ = (!crate::leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1511_ = v___x_1432_;
                        v_isShared_1512_ = v_isSharedCheck_1516_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1509_);
                        crate::leanh::lean_dec(v___x_1432_);
                        v___x_1511_ = crate::leanh::lean_box(0);
                        v_isShared_1512_ = v_isSharedCheck_1516_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1438_ = l_Lean_MVarId_congr_x3f___lam__0___closed__1;
                v___x_1439_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1440_ = l_Lean_Expr_isAppOfArity(v_a_1434_, v___x_1438_, v___x_1439_);
                if v___x_1440_ == 0 {
                    crate::leanh::lean_dec(v_a_1434_);
                    crate::leanh::lean_dec(v_mvarId_1425_);
                    v___x_1441_ = crate::leanh::lean_box(0);
                    if v_isShared_1437_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1441_);
                        v___x_1443_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
                        v___x_1443_ = v_reuseFailAlloc_1444_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1445_ = l_Lean_Expr_appFn_x21(v_a_1434_);
                    crate::leanh::lean_dec(v_a_1434_);
                    v___x_1446_ = l_Lean_Expr_appArg_x21(v___x_1445_);
                    crate::leanh::lean_dec_ref(v___x_1445_);
                    v___x_1447_ = l_Lean_Expr_cleanupAnnotations(v___x_1446_);
                    v___x_1448_ = l_Lean_Expr_isApp(v___x_1447_);
                    if v___x_1448_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1447_);
                        crate::leanh::lean_dec(v_mvarId_1425_);
                        v___x_1449_ = crate::leanh::lean_box(0);
                        if v_isShared_1437_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1436_, 0, v___x_1449_);
                            v___x_1451_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1452_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
                            v___x_1451_ = v_reuseFailAlloc_1452_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1436_);
                        v___x_1453_ = l_Lean_Expr_getAppFn(v___x_1447_);
                        v___x_1454_ = 0;
                        v___x_1455_ = l_Lean_Expr_getAppNumArgs(v___x_1447_);
                        crate::leanh::lean_dec_ref(v___x_1447_);
                        v___x_1456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1456_, 0, v___x_1455_);
                        v___x_1457_ = l_Lean_Meta_mkCongrSimp_x3f(
                            v___x_1453_,
                            v___x_1454_,
                            v___x_1456_,
                            v___y_1427_,
                            v___y_1428_,
                            v___y_1429_,
                            v___y_1430_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1457_) == 0 {
                            v_a_1458_ = crate::leanh::lean_ctor_get(v___x_1457_, 0);
                            v_isSharedCheck_1491_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1457_)) as u8;
                            if v_isSharedCheck_1491_ == 0 {
                                v___x_1460_ = v___x_1457_;
                                v_isShared_1461_ = v_isSharedCheck_1491_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1458_);
                                crate::leanh::lean_dec(v___x_1457_);
                                v___x_1460_ = crate::leanh::lean_box(0);
                                v_isShared_1461_ = v_isSharedCheck_1491_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_1425_);
                            v_a_1492_ = crate::leanh::lean_ctor_get(v___x_1457_, 0);
                            v_isSharedCheck_1499_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1457_)) as u8;
                            if v_isSharedCheck_1499_ == 0 {
                                v___x_1494_ = v___x_1457_;
                                v_isShared_1495_ = v_isSharedCheck_1499_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1492_);
                                crate::leanh::lean_dec(v___x_1457_);
                                v___x_1494_ = crate::leanh::lean_box(0);
                                v_isShared_1495_ = v_isSharedCheck_1499_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1443_;
            }
            3 => {
                return v___x_1451_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_1458_) == 1 {
                    crate::leanh::lean_del_object(v___x_1460_);
                    v_val_1462_ = crate::leanh::lean_ctor_get(v_a_1458_, 0);
                    v_isSharedCheck_1486_ = (!crate::leanh::lean_is_exclusive(v_a_1458_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1464_ = v_a_1458_;
                        v_isShared_1465_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1462_);
                        crate::leanh::lean_dec(v_a_1458_);
                        v___x_1464_ = crate::leanh::lean_box(0);
                        v_isShared_1465_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1458_);
                    crate::leanh::lean_dec(v_mvarId_1425_);
                    v___x_1487_ = crate::leanh::lean_box(0);
                    if v_isShared_1461_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1487_);
                        v___x_1489_ = v___x_1460_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
                        v___x_1489_ = v_reuseFailAlloc_1490_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1466_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
                    v_mvarId_1425_,
                    v_val_1462_,
                    v___y_1427_,
                    v___y_1428_,
                    v___y_1429_,
                    v___y_1430_,
                );
                if crate::leanh::lean_obj_tag(v___x_1466_) == 0 {
                    v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                    v_isSharedCheck_1477_ = (!crate::leanh::lean_is_exclusive(v___x_1466_)) as u8;
                    if v_isSharedCheck_1477_ == 0 {
                        v___x_1469_ = v___x_1466_;
                        v_isShared_1470_ = v_isSharedCheck_1477_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1467_);
                        crate::leanh::lean_dec(v___x_1466_);
                        v___x_1469_ = crate::leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1477_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1464_);
                    v_a_1478_ = crate::leanh::lean_ctor_get(v___x_1466_, 0);
                    v_isSharedCheck_1485_ = (!crate::leanh::lean_is_exclusive(v___x_1466_)) as u8;
                    if v_isSharedCheck_1485_ == 0 {
                        v___x_1480_ = v___x_1466_;
                        v_isShared_1481_ = v_isSharedCheck_1485_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1478_);
                        crate::leanh::lean_dec(v___x_1466_);
                        v___x_1480_ = crate::leanh::lean_box(0);
                        v_isShared_1481_ = v_isSharedCheck_1485_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1464_, 0, v_a_1467_);
                    v___x_1472_ = v___x_1464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1467_);
                    v___x_1472_ = v_reuseFailAlloc_1476_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1469_, 0, v___x_1472_);
                    v___x_1474_ = v___x_1469_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
                    v___x_1474_ = v_reuseFailAlloc_1475_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1474_;
            }
            9 => {
                if v_isShared_1481_ == 0 {
                    v___x_1483_ = v___x_1480_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
                    v___x_1483_ = v_reuseFailAlloc_1484_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1483_;
            }
            11 => {
                return v___x_1489_;
            }
            12 => {
                if v_isShared_1495_ == 0 {
                    v___x_1497_ = v___x_1494_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
                    v___x_1497_ = v_reuseFailAlloc_1498_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1497_;
            }
            14 => {
                if v_isShared_1504_ == 0 {
                    v___x_1506_ = v___x_1503_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1506_;
            }
            16 => {
                if v_isShared_1512_ == 0 {
                    v___x_1514_ = v___x_1511_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
                    v___x_1514_ = v_reuseFailAlloc_1515_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_congr_x3f___lam__0___boxed(
    mut v_mvarId_1517_: *mut crate::leanh::LeanObject,
    mut v___x_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_MVarId_congr_x3f___lam__0(
        v_mvarId_1517_,
        v___x_1518_,
        v___y_1519_,
        v___y_1520_,
        v___y_1521_,
        v___y_1522_,
    );
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    crate::leanh::lean_dec(v___y_1520_);
    crate::leanh::lean_dec_ref(v___y_1519_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(
    mut v_x_x3f_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___y_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1538_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_a_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1531_ = l_Lean_Meta_saveState___redArg(v___y_1527_, v___y_1529_);
                if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v___x_1531_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1534_ = v___x_1531_;
                        v_isShared_1535_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1532_);
                        crate::leanh::lean_dec(v___x_1531_);
                        v___x_1534_ = crate::leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_x3f_1525_);
                    v_a_1577_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    v_isSharedCheck_1584_ = (!crate::leanh::lean_is_exclusive(v___x_1531_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v___x_1579_ = v___x_1531_;
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1577_);
                        crate::leanh::lean_dec(v___x_1531_);
                        v___x_1579_ = crate::leanh::lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1529_);
                crate::leanh::lean_inc_ref(v___y_1528_);
                crate::leanh::lean_inc(v___y_1527_);
                crate::leanh::lean_inc_ref(v___y_1526_);
                v___x_1563_ = crate::leanh::lean_apply_5(
                    v_x_x3f_1525_,
                    v___y_1526_,
                    v___y_1527_,
                    v___y_1528_,
                    v___y_1529_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1563_) == 0 {
                    v_a_1564_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                    crate::leanh::lean_inc(v_a_1564_);
                    if crate::leanh::lean_obj_tag(v_a_1564_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1563_, 1);
                        v___x_1565_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_1532_,
                            v___y_1527_,
                            v___y_1529_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1565_) == 0 {
                            crate::leanh::lean_del_object(v___x_1534_);
                            crate::leanh::lean_dec(v_a_1532_);
                            v_isSharedCheck_1572_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1565_)) as u8;
                            if v_isSharedCheck_1572_ == 0 {
                                v_unused_1573_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                                crate::leanh::lean_dec(v_unused_1573_);
                                v___x_1567_ = v___x_1565_;
                                v_isShared_1568_ = v_isSharedCheck_1572_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1565_);
                                v___x_1567_ = crate::leanh::lean_box(0);
                                v_isShared_1568_ = v_isSharedCheck_1572_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v_a_1574_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                            crate::leanh::lean_inc(v_a_1574_);
                            crate::leanh::lean_dec_ref_known(v___x_1565_, 1);
                            v_a_1560_ = v_a_1574_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_1564_, 1);
                        crate::leanh::lean_del_object(v___x_1534_);
                        crate::leanh::lean_dec(v_a_1532_);
                        return v___x_1563_;
                    }
                } else {
                    v_a_1575_ = crate::leanh::lean_ctor_get(v___x_1563_, 0);
                    crate::leanh::lean_inc(v_a_1575_);
                    crate::leanh::lean_dec_ref_known(v___x_1563_, 1);
                    v_a_1560_ = v_a_1575_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                if v___y_1538_ == 0 {
                    crate::leanh::lean_del_object(v___x_1534_);
                    v___x_1539_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1532_,
                        v___y_1527_,
                        v___y_1529_,
                    );
                    crate::leanh::lean_dec(v_a_1532_);
                    if crate::leanh::lean_obj_tag(v___x_1539_) == 0 {
                        v_isSharedCheck_1546_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1539_)) as u8;
                        if v_isSharedCheck_1546_ == 0 {
                            v_unused_1547_ = crate::leanh::lean_ctor_get(v___x_1539_, 0);
                            crate::leanh::lean_dec(v_unused_1547_);
                            v___x_1541_ = v___x_1539_;
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1539_);
                            v___x_1541_ = crate::leanh::lean_box(0);
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1537_);
                        v_a_1548_ = crate::leanh::lean_ctor_get(v___x_1539_, 0);
                        v_isSharedCheck_1555_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1539_)) as u8;
                        if v_isSharedCheck_1555_ == 0 {
                            v___x_1550_ = v___x_1539_;
                            v_isShared_1551_ = v_isSharedCheck_1555_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1548_);
                            crate::leanh::lean_dec(v___x_1539_);
                            v___x_1550_ = crate::leanh::lean_box(0);
                            v_isShared_1551_ = v_isSharedCheck_1555_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1532_);
                    if v_isShared_1535_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1534_, 1);
                        crate::leanh::lean_ctor_set(v___x_1534_, 0, v___y_1537_);
                        v___x_1557_ = v___x_1534_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___y_1537_);
                        v___x_1557_ = v_reuseFailAlloc_1558_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1542_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1541_, 1);
                    crate::leanh::lean_ctor_set(v___x_1541_, 0, v___y_1537_);
                    v___x_1544_ = v___x_1541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___y_1537_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1544_;
            }
            5 => {
                if v_isShared_1551_ == 0 {
                    v___x_1553_ = v___x_1550_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
                    v___x_1553_ = v_reuseFailAlloc_1554_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1553_;
            }
            7 => {
                return v___x_1557_;
            }
            8 => {
                v___x_1561_ = l_Lean_Exception_isInterrupt(v_a_1560_);
                if v___x_1561_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_1560_);
                    v___x_1562_ = l_Lean_Exception_isRuntime(v_a_1560_);
                    v___y_1537_ = v_a_1560_;
                    v___y_1538_ = v___x_1562_;
                    state = 2;
                    continue;
                } else {
                    v___y_1537_ = v_a_1560_;
                    v___y_1538_ = v___x_1561_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                if v_isShared_1568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1567_, 0, v_a_1564_);
                    v___x_1570_ = v___x_1567_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1564_);
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1570_;
            }
            11 => {
                if v_isShared_1580_ == 0 {
                    v___x_1582_ = v___x_1579_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_x3f_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
    crate::leanh::lean_dec(v___y_1589_);
    crate::leanh::lean_dec_ref(v___y_1588_);
    crate::leanh::lean_dec(v___y_1587_);
    crate::leanh::lean_dec_ref(v___y_1586_);
    return v_res_1591_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
    mut v_x_x3f_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: u8 = 0;
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1604_: u8 = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut v_unused_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
                if crate::leanh::lean_obj_tag(v___x_1598_) == 0 {
                    return v___x_1598_;
                } else {
                    v_a_1599_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                    crate::leanh::lean_inc(v_a_1599_);
                    v___x_1611_ = l_Lean_Exception_isInterrupt(v_a_1599_);
                    if v___x_1611_ == 0 {
                        v___x_1612_ = l_Lean_Exception_isRuntime(v_a_1599_);
                        v___y_1601_ = v___x_1612_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1599_);
                        v___y_1601_ = v___x_1611_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1601_ == 0 {
                    v_isSharedCheck_1609_ = (!crate::leanh::lean_is_exclusive(v___x_1598_)) as u8;
                    if v_isSharedCheck_1609_ == 0 {
                        v_unused_1610_ = crate::leanh::lean_ctor_get(v___x_1598_, 0);
                        crate::leanh::lean_dec(v_unused_1610_);
                        v___x_1603_ = v___x_1598_;
                        v_isShared_1604_ = v_isSharedCheck_1609_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1598_);
                        v___x_1603_ = crate::leanh::lean_box(0);
                        v_isShared_1604_ = v_isSharedCheck_1609_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_1598_;
                }
            }
            2 => {
                v___x_1605_ = crate::leanh::lean_box(0);
                if v_isShared_1604_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1603_, 0);
                    crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1605_);
                    v___x_1607_ = v___x_1603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
                    v___x_1607_ = v_reuseFailAlloc_1608_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg___boxed(
    mut v_x_x3f_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
        v_x_x3f_1613_,
        v___y_1614_,
        v___y_1615_,
        v___y_1616_,
        v___y_1617_,
    );
    crate::leanh::lean_dec(v___y_1617_);
    crate::leanh::lean_dec_ref(v___y_1616_);
    crate::leanh::lean_dec(v___y_1615_);
    crate::leanh::lean_dec_ref(v___y_1614_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(
    mut v_00_u03b1_1620_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
        v_x_x3f_1621_,
        v___y_1622_,
        v___y_1623_,
        v___y_1624_,
        v___y_1625_,
    );
    return v___x_1627_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed(
    mut v_00_u03b1_1628_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(
        v_00_u03b1_1628_,
        v_x_x3f_1629_,
        v___y_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
    );
    crate::leanh::lean_dec(v___y_1633_);
    crate::leanh::lean_dec_ref(v___y_1632_);
    crate::leanh::lean_dec(v___y_1631_);
    crate::leanh::lean_dec_ref(v___y_1630_);
    return v_res_1635_;
}
pub unsafe fn l_Lean_MVarId_congr_x3f(
    mut v_mvarId_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_MVarId_congr_x3f___closed__1;
    crate::leanh::lean_inc(v_mvarId_1639_);
    v___f_1646_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_congr_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1646_, 0, v_mvarId_1639_);
    crate::leanh::lean_closure_set(v___f_1646_, 1, v___x_1645_);
    v___x_1647_ = crate::leanh::lean_alloc_closure(
        l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1647_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1647_, 1, v___f_1646_);
    v___x_1648_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
        v_mvarId_1639_,
        v___x_1647_,
        v_a_1640_,
        v_a_1641_,
        v_a_1642_,
        v_a_1643_,
    );
    return v___x_1648_;
}
pub unsafe fn l_Lean_MVarId_congr_x3f___boxed(
    mut v_mvarId_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ =
        l_Lean_MVarId_congr_x3f(v_mvarId_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
    crate::leanh::lean_dec(v_a_1653_);
    crate::leanh::lean_dec_ref(v_a_1652_);
    crate::leanh::lean_dec(v_a_1651_);
    crate::leanh::lean_dec_ref(v_a_1650_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(
    mut v_00_u03b1_1656_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_x_x3f_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(v_00_u03b1_1664_, v_x_x3f_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
    crate::leanh::lean_dec(v___y_1669_);
    crate::leanh::lean_dec_ref(v___y_1668_);
    crate::leanh::lean_dec(v___y_1667_);
    crate::leanh::lean_dec_ref(v___y_1666_);
    return v_res_1671_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__0(
    mut v_a_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1685_: u8 = 0;
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1710_: u8 = 0;
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1675_);
                v___x_1681_ = l_Lean_MVarId_getType_x27(
                    v_a_1675_,
                    v___y_1676_,
                    v___y_1677_,
                    v___y_1678_,
                    v___y_1679_,
                );
                if crate::leanh::lean_obj_tag(v___x_1681_) == 0 {
                    v_a_1682_ = crate::leanh::lean_ctor_get(v___x_1681_, 0);
                    v_isSharedCheck_1732_ = (!crate::leanh::lean_is_exclusive(v___x_1681_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1684_ = v___x_1681_;
                        v_isShared_1685_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1682_);
                        crate::leanh::lean_dec(v___x_1681_);
                        v___x_1684_ = crate::leanh::lean_box(0);
                        v_isShared_1685_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1675_);
                    v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1681_, 0);
                    v_isSharedCheck_1740_ = (!crate::leanh::lean_is_exclusive(v___x_1681_)) as u8;
                    if v_isSharedCheck_1740_ == 0 {
                        v___x_1735_ = v___x_1681_;
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec(v___x_1681_);
                        v___x_1735_ = crate::leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1686_ = l_Lean_MVarId_hcongr_x3f___lam__0___closed__1;
                v___x_1687_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_1688_ = l_Lean_Expr_isAppOfArity(v_a_1682_, v___x_1686_, v___x_1687_);
                if v___x_1688_ == 0 {
                    crate::leanh::lean_dec(v_a_1682_);
                    crate::leanh::lean_dec(v_a_1675_);
                    v___x_1689_ = crate::leanh::lean_box(0);
                    if v_isShared_1685_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1689_);
                        v___x_1691_ = v___x_1684_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
                        v___x_1691_ = v_reuseFailAlloc_1692_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1693_ = l_Lean_Expr_appFn_x21(v_a_1682_);
                    crate::leanh::lean_dec(v_a_1682_);
                    v___x_1694_ = l_Lean_Expr_appFn_x21(v___x_1693_);
                    crate::leanh::lean_dec_ref(v___x_1693_);
                    v___x_1695_ = l_Lean_Expr_appArg_x21(v___x_1694_);
                    crate::leanh::lean_dec_ref(v___x_1694_);
                    v___x_1696_ = l_Lean_Expr_cleanupAnnotations(v___x_1695_);
                    v___x_1697_ = l_Lean_Expr_isApp(v___x_1696_);
                    if v___x_1697_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1696_);
                        crate::leanh::lean_dec(v_a_1675_);
                        v___x_1698_ = crate::leanh::lean_box(0);
                        if v_isShared_1685_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1698_);
                            v___x_1700_ = v___x_1684_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1701_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                            v___x_1700_ = v_reuseFailAlloc_1701_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1684_);
                        v___x_1702_ = l_Lean_Expr_getAppFn(v___x_1696_);
                        v___x_1703_ = l_Lean_Expr_getAppNumArgs(v___x_1696_);
                        crate::leanh::lean_dec_ref(v___x_1696_);
                        v___x_1704_ = l_Lean_Meta_mkHCongrWithArity(
                            v___x_1702_,
                            v___x_1703_,
                            v___y_1676_,
                            v___y_1677_,
                            v___y_1678_,
                            v___y_1679_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1704_) == 0 {
                            v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                            crate::leanh::lean_inc(v_a_1705_);
                            crate::leanh::lean_dec_ref_known(v___x_1704_, 1);
                            v___x_1706_ =
                                l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
                                    v_a_1675_,
                                    v_a_1705_,
                                    v___y_1676_,
                                    v___y_1677_,
                                    v___y_1678_,
                                    v___y_1679_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_1706_) == 0 {
                                v_a_1707_ = crate::leanh::lean_ctor_get(v___x_1706_, 0);
                                v_isSharedCheck_1715_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1706_)) as u8;
                                if v_isSharedCheck_1715_ == 0 {
                                    v___x_1709_ = v___x_1706_;
                                    v_isShared_1710_ = v_isSharedCheck_1715_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1707_);
                                    crate::leanh::lean_dec(v___x_1706_);
                                    v___x_1709_ = crate::leanh::lean_box(0);
                                    v_isShared_1710_ = v_isSharedCheck_1715_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_1716_ = crate::leanh::lean_ctor_get(v___x_1706_, 0);
                                v_isSharedCheck_1723_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1706_)) as u8;
                                if v_isSharedCheck_1723_ == 0 {
                                    v___x_1718_ = v___x_1706_;
                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1716_);
                                    crate::leanh::lean_dec(v___x_1706_);
                                    v___x_1718_ = crate::leanh::lean_box(0);
                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1675_);
                            v_a_1724_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                            v_isSharedCheck_1731_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                            if v_isSharedCheck_1731_ == 0 {
                                v___x_1726_ = v___x_1704_;
                                v_isShared_1727_ = v_isSharedCheck_1731_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1724_);
                                crate::leanh::lean_dec(v___x_1704_);
                                v___x_1726_ = crate::leanh::lean_box(0);
                                v_isShared_1727_ = v_isSharedCheck_1731_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1691_;
            }
            3 => {
                return v___x_1700_;
            }
            4 => {
                v___x_1711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1711_, 0, v_a_1707_);
                if v_isShared_1710_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1709_, 0, v___x_1711_);
                    v___x_1713_ = v___x_1709_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
                    v___x_1713_ = v_reuseFailAlloc_1714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1713_;
            }
            6 => {
                if v_isShared_1719_ == 0 {
                    v___x_1721_ = v___x_1718_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1721_;
            }
            8 => {
                if v_isShared_1727_ == 0 {
                    v___x_1729_ = v___x_1726_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
                    v___x_1729_ = v_reuseFailAlloc_1730_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1729_;
            }
            10 => {
                if v_isShared_1736_ == 0 {
                    v___x_1738_ = v___x_1735_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1739_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__0___boxed(
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lean_MVarId_hcongr_x3f___lam__0(
        v_a_1741_,
        v___y_1742_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
    );
    crate::leanh::lean_dec(v___y_1745_);
    crate::leanh::lean_dec_ref(v___y_1744_);
    crate::leanh::lean_dec(v___y_1743_);
    crate::leanh::lean_dec_ref(v___y_1742_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__1(
    mut v_mvarId_1748_: *mut crate::leanh::LeanObject,
    mut v___x_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_a_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1748_);
                v___x_1755_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1748_,
                    v___x_1749_,
                    v___y_1750_,
                    v___y_1751_,
                    v___y_1752_,
                    v___y_1753_,
                );
                if crate::leanh::lean_obj_tag(v___x_1755_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1755_, 1);
                    v___x_1756_ = l_Lean_MVarId_eqOfHEq(
                        v_mvarId_1748_,
                        v___y_1750_,
                        v___y_1751_,
                        v___y_1752_,
                        v___y_1753_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                        v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                        crate::leanh::lean_inc_n(v_a_1757_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1756_, 1);
                        v___f_1758_ = crate::leanh::lean_alloc_closure(
                            l_Lean_MVarId_hcongr_x3f___lam__0___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_1758_, 0, v_a_1757_);
                        v___x_1759_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_a_1757_, v___f_1758_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
                        return v___x_1759_;
                    } else {
                        v_a_1760_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                        v_isSharedCheck_1767_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                        if v_isSharedCheck_1767_ == 0 {
                            v___x_1762_ = v___x_1756_;
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1760_);
                            crate::leanh::lean_dec(v___x_1756_);
                            v___x_1762_ = crate::leanh::lean_box(0);
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1748_);
                    v_a_1768_ = crate::leanh::lean_ctor_get(v___x_1755_, 0);
                    v_isSharedCheck_1775_ = (!crate::leanh::lean_is_exclusive(v___x_1755_)) as u8;
                    if v_isSharedCheck_1775_ == 0 {
                        v___x_1770_ = v___x_1755_;
                        v_isShared_1771_ = v_isSharedCheck_1775_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1768_);
                        crate::leanh::lean_dec(v___x_1755_);
                        v___x_1770_ = crate::leanh::lean_box(0);
                        v_isShared_1771_ = v_isSharedCheck_1775_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1763_ == 0 {
                    v___x_1765_ = v___x_1762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
                    v___x_1765_ = v_reuseFailAlloc_1766_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1765_;
            }
            3 => {
                if v_isShared_1771_ == 0 {
                    v___x_1773_ = v___x_1770_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
                    v___x_1773_ = v_reuseFailAlloc_1774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__1___boxed(
    mut v_mvarId_1776_: *mut crate::leanh::LeanObject,
    mut v___x_1777_: *mut crate::leanh::LeanObject,
    mut v___y_1778_: *mut crate::leanh::LeanObject,
    mut v___y_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Lean_MVarId_hcongr_x3f___lam__1(
        v_mvarId_1776_,
        v___x_1777_,
        v___y_1778_,
        v___y_1779_,
        v___y_1780_,
        v___y_1781_,
    );
    crate::leanh::lean_dec(v___y_1781_);
    crate::leanh::lean_dec_ref(v___y_1780_);
    crate::leanh::lean_dec(v___y_1779_);
    crate::leanh::lean_dec_ref(v___y_1778_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f(
    mut v_mvarId_1784_: *mut crate::leanh::LeanObject,
    mut v_a_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Lean_MVarId_congr_x3f___closed__1;
    v___f_1791_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_hcongr_x3f___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1791_, 0, v_mvarId_1784_);
    crate::leanh::lean_closure_set(v___f_1791_, 1, v___x_1790_);
    v___x_1792_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
        v___f_1791_,
        v_a_1785_,
        v_a_1786_,
        v_a_1787_,
        v_a_1788_,
    );
    return v___x_1792_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___boxed(
    mut v_mvarId_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ =
        l_Lean_MVarId_hcongr_x3f(v_mvarId_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
    crate::leanh::lean_dec(v_a_1797_);
    crate::leanh::lean_dec_ref(v_a_1796_);
    crate::leanh::lean_dec(v_a_1795_);
    crate::leanh::lean_dec_ref(v_a_1794_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
    mut v_x_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1817_: u8 = 0;
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___y_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut v_unused_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1837_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut v_a_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1851_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1806_ = l_Lean_Meta_saveState___redArg(v___y_1802_, v___y_1804_);
                if crate::leanh::lean_obj_tag(v___x_1806_) == 0 {
                    v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    crate::leanh::lean_inc(v_a_1807_);
                    crate::leanh::lean_dec_ref_known(v___x_1806_, 1);
                    crate::leanh::lean_inc(v___y_1804_);
                    crate::leanh::lean_inc_ref(v___y_1803_);
                    crate::leanh::lean_inc(v___y_1802_);
                    crate::leanh::lean_inc_ref(v___y_1801_);
                    v___x_1808_ = crate::leanh::lean_apply_5(
                        v_x_1800_,
                        v___y_1801_,
                        v___y_1802_,
                        v___y_1803_,
                        v___y_1804_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1808_) == 0 {
                        crate::leanh::lean_dec(v_a_1807_);
                        v_a_1809_ = crate::leanh::lean_ctor_get(v___x_1808_, 0);
                        v_isSharedCheck_1817_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1808_)) as u8;
                        if v_isSharedCheck_1817_ == 0 {
                            v___x_1811_ = v___x_1808_;
                            v_isShared_1812_ = v_isSharedCheck_1817_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1809_);
                            crate::leanh::lean_dec(v___x_1808_);
                            v___x_1811_ = crate::leanh::lean_box(0);
                            v_isShared_1812_ = v_isSharedCheck_1817_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1808_, 0);
                        v_isSharedCheck_1847_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1808_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v___x_1820_ = v___x_1808_;
                            v_isShared_1821_ = v_isSharedCheck_1847_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1818_);
                            crate::leanh::lean_dec(v___x_1808_);
                            v___x_1820_ = crate::leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_1847_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1800_);
                    v_a_1848_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1855_ = (!crate::leanh::lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1850_ = v___x_1806_;
                        v_isShared_1851_ = v_isSharedCheck_1855_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1848_);
                        crate::leanh::lean_dec(v___x_1806_);
                        v___x_1850_ = crate::leanh::lean_box(0);
                        v_isShared_1851_ = v_isSharedCheck_1855_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1813_, 0, v_a_1809_);
                if v_isShared_1812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1813_);
                    v___x_1815_ = v___x_1811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
                    v___x_1815_ = v_reuseFailAlloc_1816_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1815_;
            }
            3 => {
                v___x_1845_ = l_Lean_Exception_isInterrupt(v_a_1818_);
                if v___x_1845_ == 0 {
                    crate::leanh::lean_inc(v_a_1818_);
                    v___x_1846_ = l_Lean_Exception_isRuntime(v_a_1818_);
                    v___y_1823_ = v___x_1846_;
                    state = 4;
                    continue;
                } else {
                    v___y_1823_ = v___x_1845_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_1823_ == 0 {
                    crate::leanh::lean_del_object(v___x_1820_);
                    crate::leanh::lean_dec(v_a_1818_);
                    v___x_1824_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1807_,
                        v___y_1802_,
                        v___y_1804_,
                    );
                    crate::leanh::lean_dec(v_a_1807_);
                    if crate::leanh::lean_obj_tag(v___x_1824_) == 0 {
                        v_isSharedCheck_1832_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1824_)) as u8;
                        if v_isSharedCheck_1832_ == 0 {
                            v_unused_1833_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                            crate::leanh::lean_dec(v_unused_1833_);
                            v___x_1826_ = v___x_1824_;
                            v_isShared_1827_ = v_isSharedCheck_1832_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1824_);
                            v___x_1826_ = crate::leanh::lean_box(0);
                            v_isShared_1827_ = v_isSharedCheck_1832_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1834_ = crate::leanh::lean_ctor_get(v___x_1824_, 0);
                        v_isSharedCheck_1841_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1824_)) as u8;
                        if v_isSharedCheck_1841_ == 0 {
                            v___x_1836_ = v___x_1824_;
                            v_isShared_1837_ = v_isSharedCheck_1841_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1834_);
                            crate::leanh::lean_dec(v___x_1824_);
                            v___x_1836_ = crate::leanh::lean_box(0);
                            v_isShared_1837_ = v_isSharedCheck_1841_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1807_);
                    if v_isShared_1821_ == 0 {
                        v___x_1843_ = v___x_1820_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1818_);
                        v___x_1843_ = v_reuseFailAlloc_1844_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1828_ = crate::leanh::lean_box(0);
                if v_isShared_1827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1828_);
                    v___x_1830_ = v___x_1826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1830_;
            }
            7 => {
                if v_isShared_1837_ == 0 {
                    v___x_1839_ = v___x_1836_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
                    v___x_1839_ = v_reuseFailAlloc_1840_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1839_;
            }
            9 => {
                return v___x_1843_;
            }
            10 => {
                if v_isShared_1851_ == 0 {
                    v___x_1853_ = v___x_1850_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
                    v___x_1853_ = v_reuseFailAlloc_1854_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg___boxed(
    mut v_x_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
        v_x_1856_,
        v___y_1857_,
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
    );
    crate::leanh::lean_dec(v___y_1860_);
    crate::leanh::lean_dec_ref(v___y_1859_);
    crate::leanh::lean_dec(v___y_1858_);
    crate::leanh::lean_dec_ref(v___y_1857_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(
    mut v_00_u03b1_1863_: *mut crate::leanh::LeanObject,
    mut v_x_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
        v_x_1864_,
        v___y_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
    );
    return v___x_1870_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___boxed(
    mut v_00_u03b1_1871_: *mut crate::leanh::LeanObject,
    mut v_x_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(
        v_00_u03b1_1871_,
        v_x_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
    );
    crate::leanh::lean_dec(v___y_1876_);
    crate::leanh::lean_dec_ref(v___y_1875_);
    crate::leanh::lean_dec(v___y_1874_);
    crate::leanh::lean_dec_ref(v___y_1873_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(
    mut v_msgData_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = lean_st_ref_get(v___y_1883_);
    v_env_1886_ = crate::leanh::lean_ctor_get(v___x_1885_, 0);
    crate::leanh::lean_inc_ref(v_env_1886_);
    crate::leanh::lean_dec(v___x_1885_);
    v___x_1887_ = lean_st_ref_get(v___y_1881_);
    v_mctx_1888_ = crate::leanh::lean_ctor_get(v___x_1887_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1888_);
    crate::leanh::lean_dec(v___x_1887_);
    v_lctx_1889_ = crate::leanh::lean_ctor_get(v___y_1880_, 2);
    v_options_1890_ = crate::leanh::lean_ctor_get(v___y_1882_, 2);
    crate::leanh::lean_inc_ref(v_options_1890_);
    crate::leanh::lean_inc_ref(v_lctx_1889_);
    v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1891_, 0, v_env_1886_);
    crate::leanh::lean_ctor_set(v___x_1891_, 1, v_mctx_1888_);
    crate::leanh::lean_ctor_set(v___x_1891_, 2, v_lctx_1889_);
    crate::leanh::lean_ctor_set(v___x_1891_, 3, v_options_1890_);
    v___x_1892_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    crate::leanh::lean_ctor_set(v___x_1892_, 1, v_msgData_1879_);
    v___x_1893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
    return v___x_1893_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(
    mut v_msgData_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1900_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msgData_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
    crate::leanh::lean_dec(v___y_1898_);
    crate::leanh::lean_dec_ref(v___y_1897_);
    crate::leanh::lean_dec(v___y_1896_);
    crate::leanh::lean_dec_ref(v___y_1895_);
    return v_res_1900_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
    mut v_msg_1901_: *mut crate::leanh::LeanObject,
    mut v___y_1902_: *mut crate::leanh::LeanObject,
    mut v___y_1903_: *mut crate::leanh::LeanObject,
    mut v___y_1904_: *mut crate::leanh::LeanObject,
    mut v___y_1905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1907_ = crate::leanh::lean_ctor_get(v___y_1904_, 5);
                v___x_1908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                v_a_1909_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                v_isSharedCheck_1917_ = (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                if v_isSharedCheck_1917_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    v_isShared_1912_ = v_isSharedCheck_1917_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1909_);
                    crate::leanh::lean_dec(v___x_1908_);
                    v___x_1911_ = crate::leanh::lean_box(0);
                    v_isShared_1912_ = v_isSharedCheck_1917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1907_);
                v___x_1913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1913_, 0, v_ref_1907_);
                crate::leanh::lean_ctor_set(v___x_1913_, 1, v_a_1909_);
                if v_isShared_1912_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1911_, 1);
                    crate::leanh::lean_ctor_set(v___x_1911_, 0, v___x_1913_);
                    v___x_1915_ = v___x_1911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(
    mut v_msg_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
        v_msg_1918_,
        v___y_1919_,
        v___y_1920_,
        v___y_1921_,
        v___y_1922_,
    );
    crate::leanh::lean_dec(v___y_1922_);
    crate::leanh::lean_dec_ref(v___y_1921_);
    crate::leanh::lean_dec(v___y_1920_);
    crate::leanh::lean_dec_ref(v___y_1919_);
    return v_res_1924_;
}
pub unsafe fn _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1;
    v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3;
    v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f___lam__0(
    mut v___x_1935_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___y_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v_head_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_unused_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_a_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_1935_);
                v___x_1942_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v___x_1935_,
                    v___y_1937_,
                    v___y_1938_,
                    v___y_1939_,
                    v___y_1940_,
                );
                if crate::leanh::lean_obj_tag(v___x_1942_) == 0 {
                    v_a_1943_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                    crate::leanh::lean_inc(v_a_1943_);
                    crate::leanh::lean_dec_ref_known(v___x_1942_, 1);
                    v___x_1944_ = 0;
                    v___x_1945_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0;
                    v___x_1946_ = crate::leanh::lean_box(0);
                    v___x_1947_ = l_Lean_MVarId_apply(
                        v_mvarId_1936_,
                        v_a_1943_,
                        v___x_1945_,
                        v___x_1946_,
                        v___y_1937_,
                        v___y_1938_,
                        v___y_1939_,
                        v___y_1940_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1947_) == 0 {
                        v_a_1948_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                        v_isSharedCheck_1986_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1947_)) as u8;
                        if v_isSharedCheck_1986_ == 0 {
                            v___x_1950_ = v___x_1947_;
                            v_isShared_1951_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1948_);
                            crate::leanh::lean_dec(v___x_1947_);
                            v___x_1950_ = crate::leanh::lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1935_);
                        return v___x_1947_;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1936_);
                    crate::leanh::lean_dec(v___x_1935_);
                    v_a_1987_ = crate::leanh::lean_ctor_get(v___x_1942_, 0);
                    v_isSharedCheck_1994_ = (!crate::leanh::lean_is_exclusive(v___x_1942_)) as u8;
                    if v_isSharedCheck_1994_ == 0 {
                        v___x_1989_ = v___x_1942_;
                        v_isShared_1990_ = v_isSharedCheck_1994_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1987_);
                        crate::leanh::lean_dec(v___x_1942_);
                        v___x_1989_ = crate::leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_1994_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1948_) == 1 {
                    v_tail_1963_ = crate::leanh::lean_ctor_get(v_a_1948_, 1);
                    crate::leanh::lean_inc(v_tail_1963_);
                    if crate::leanh::lean_obj_tag(v_tail_1963_) == 1 {
                        crate::leanh::lean_dec(v___x_1935_);
                        v_head_1964_ = crate::leanh::lean_ctor_get(v_a_1948_, 0);
                        v_isSharedCheck_1984_ = (!crate::leanh::lean_is_exclusive(v_a_1948_)) as u8;
                        if v_isSharedCheck_1984_ == 0 {
                            v_unused_1985_ = crate::leanh::lean_ctor_get(v_a_1948_, 1);
                            crate::leanh::lean_dec(v_unused_1985_);
                            v___x_1966_ = v_a_1948_;
                            v_isShared_1967_ = v_isSharedCheck_1984_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_1964_);
                            crate::leanh::lean_dec(v_a_1948_);
                            v___x_1966_ = crate::leanh::lean_box(0);
                            v_isShared_1967_ = v_isSharedCheck_1984_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_1963_);
                        crate::leanh::lean_dec_ref_known(v_a_1948_, 2);
                        crate::leanh::lean_del_object(v___x_1950_);
                        v___y_1953_ = v___y_1937_;
                        v___y_1954_ = v___y_1938_;
                        v___y_1955_ = v___y_1939_;
                        v___y_1956_ = v___y_1940_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1950_);
                    crate::leanh::lean_dec(v_a_1948_);
                    v___y_1953_ = v___y_1937_;
                    v___y_1954_ = v___y_1938_;
                    v___y_1955_ = v___y_1939_;
                    v___y_1956_ = v___y_1940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1957_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once
                    ),
                    _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2,
                );
                v___x_1958_ = l_Lean_MessageData_ofConstName(v___x_1935_, v___x_1944_);
                v___x_1959_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1957_);
                crate::leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
                v___x_1960_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once
                    ),
                    _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4,
                );
                v___x_1961_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1959_);
                crate::leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
                v___x_1962_ =
                    l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
                        v___x_1961_,
                        v___y_1953_,
                        v___y_1954_,
                        v___y_1955_,
                        v___y_1956_,
                    );
                return v___x_1962_;
            }
            3 => {
                v_head_1968_ = crate::leanh::lean_ctor_get(v_tail_1963_, 0);
                v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v_tail_1963_)) as u8;
                if v_isSharedCheck_1982_ == 0 {
                    v_unused_1983_ = crate::leanh::lean_ctor_get(v_tail_1963_, 1);
                    crate::leanh::lean_dec(v_unused_1983_);
                    v___x_1970_ = v_tail_1963_;
                    v_isShared_1971_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_head_1968_);
                    crate::leanh::lean_dec(v_tail_1963_);
                    v___x_1970_ = crate::leanh::lean_box(0);
                    v_isShared_1971_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1972_ = crate::leanh::lean_box(0);
                if v_isShared_1971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1970_, 1, v___x_1972_);
                    v___x_1974_ = v___x_1970_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_head_1968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1972_);
                    v___x_1974_ = v_reuseFailAlloc_1981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1966_, 1, v___x_1974_);
                    v___x_1976_ = v___x_1966_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_head_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1974_);
                    v___x_1976_ = v_reuseFailAlloc_1980_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1976_);
                    v___x_1978_ = v___x_1950_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
                    v___x_1978_ = v_reuseFailAlloc_1979_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1978_;
            }
            8 => {
                if v_isShared_1990_ == 0 {
                    v___x_1992_ = v___x_1989_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
                    v___x_1992_ = v_reuseFailAlloc_1993_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f___lam__0___boxed(
    mut v___x_1995_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1996_: *mut crate::leanh::LeanObject,
    mut v___y_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_MVarId_congrImplies_x3f___lam__0(
        v___x_1995_,
        v_mvarId_1996_,
        v___y_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
    );
    crate::leanh::lean_dec(v___y_2000_);
    crate::leanh::lean_dec_ref(v___y_1999_);
    crate::leanh::lean_dec(v___y_1998_);
    crate::leanh::lean_dec_ref(v___y_1997_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f(
    mut v_mvarId_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v_a_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lean_MVarId_congrImplies_x3f___closed__1;
    v___f_2013_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_congrImplies_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2013_, 0, v___x_2012_);
    crate::leanh::lean_closure_set(v___f_2013_, 1, v_mvarId_2006_);
    v___x_2014_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
        v___f_2013_,
        v_a_2007_,
        v_a_2008_,
        v_a_2009_,
        v_a_2010_,
    );
    return v___x_2014_;
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f___boxed(
    mut v_mvarId_2015_: *mut crate::leanh::LeanObject,
    mut v_a_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
    mut v_a_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ =
        l_Lean_MVarId_congrImplies_x3f(v_mvarId_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
    crate::leanh::lean_dec(v_a_2019_);
    crate::leanh::lean_dec_ref(v_a_2018_);
    crate::leanh::lean_dec(v_a_2017_);
    crate::leanh::lean_dec_ref(v_a_2016_);
    return v_res_2021_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(
    mut v_00_u03b1_2022_: *mut crate::leanh::LeanObject,
    mut v_msg_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
        v_msg_2023_,
        v___y_2024_,
        v___y_2025_,
        v___y_2026_,
        v___y_2027_,
    );
    return v___x_2029_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___boxed(
    mut v_00_u03b1_2030_: *mut crate::leanh::LeanObject,
    mut v_msg_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2037_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(
        v_00_u03b1_2030_,
        v_msg_2031_,
        v___y_2032_,
        v___y_2033_,
        v___y_2034_,
        v___y_2035_,
    );
    crate::leanh::lean_dec(v___y_2035_);
    crate::leanh::lean_dec_ref(v___y_2034_);
    crate::leanh::lean_dec(v___y_2033_);
    crate::leanh::lean_dec_ref(v___y_2032_);
    return v_res_2037_;
}
pub unsafe fn _init_l_Lean_MVarId_congrCore___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_MVarId_congrCore___closed__1;
    v___x_2042_ = l_Lean_MessageData_ofFormat(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn _init_l_Lean_MVarId_congrCore___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__2_once),
        _init_l_Lean_MVarId_congrCore___closed__2,
    );
    v___x_2044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_MVarId_congrCore(
    mut v_mvarId_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
    mut v_a_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v_val_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_val_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v_val_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v_a_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_a_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_2045_);
                v___x_2051_ = l_Lean_MVarId_congr_x3f(
                    v_mvarId_2045_,
                    v_a_2046_,
                    v_a_2047_,
                    v_a_2048_,
                    v_a_2049_,
                );
                if crate::leanh::lean_obj_tag(v___x_2051_) == 0 {
                    v_a_2052_ = crate::leanh::lean_ctor_get(v___x_2051_, 0);
                    v_isSharedCheck_2099_ = (!crate::leanh::lean_is_exclusive(v___x_2051_)) as u8;
                    if v_isSharedCheck_2099_ == 0 {
                        v___x_2054_ = v___x_2051_;
                        v_isShared_2055_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2052_);
                        crate::leanh::lean_dec(v___x_2051_);
                        v___x_2054_ = crate::leanh::lean_box(0);
                        v_isShared_2055_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_2045_);
                    v_a_2100_ = crate::leanh::lean_ctor_get(v___x_2051_, 0);
                    v_isSharedCheck_2107_ = (!crate::leanh::lean_is_exclusive(v___x_2051_)) as u8;
                    if v_isSharedCheck_2107_ == 0 {
                        v___x_2102_ = v___x_2051_;
                        v_isShared_2103_ = v_isSharedCheck_2107_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2100_);
                        crate::leanh::lean_dec(v___x_2051_);
                        v___x_2102_ = crate::leanh::lean_box(0);
                        v_isShared_2103_ = v_isSharedCheck_2107_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2052_) == 1 {
                    crate::leanh::lean_dec(v_mvarId_2045_);
                    v_val_2056_ = crate::leanh::lean_ctor_get(v_a_2052_, 0);
                    crate::leanh::lean_inc(v_val_2056_);
                    crate::leanh::lean_dec_ref_known(v_a_2052_, 1);
                    if v_isShared_2055_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2054_, 0, v_val_2056_);
                        v___x_2058_ = v___x_2054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_val_2056_);
                        v___x_2058_ = v_reuseFailAlloc_2059_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2054_);
                    crate::leanh::lean_dec(v_a_2052_);
                    crate::leanh::lean_inc(v_mvarId_2045_);
                    v___x_2060_ = l_Lean_MVarId_hcongr_x3f(
                        v_mvarId_2045_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2060_) == 0 {
                        v_a_2061_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                        v_isSharedCheck_2090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2060_)) as u8;
                        if v_isSharedCheck_2090_ == 0 {
                            v___x_2063_ = v___x_2060_;
                            v_isShared_2064_ = v_isSharedCheck_2090_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2061_);
                            crate::leanh::lean_dec(v___x_2060_);
                            v___x_2063_ = crate::leanh::lean_box(0);
                            v_isShared_2064_ = v_isSharedCheck_2090_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_2045_);
                        v_a_2091_ = crate::leanh::lean_ctor_get(v___x_2060_, 0);
                        v_isSharedCheck_2098_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2060_)) as u8;
                        if v_isSharedCheck_2098_ == 0 {
                            v___x_2093_ = v___x_2060_;
                            v_isShared_2094_ = v_isSharedCheck_2098_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2091_);
                            crate::leanh::lean_dec(v___x_2060_);
                            v___x_2093_ = crate::leanh::lean_box(0);
                            v_isShared_2094_ = v_isSharedCheck_2098_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2058_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2061_) == 1 {
                    crate::leanh::lean_dec(v_mvarId_2045_);
                    v_val_2065_ = crate::leanh::lean_ctor_get(v_a_2061_, 0);
                    crate::leanh::lean_inc(v_val_2065_);
                    crate::leanh::lean_dec_ref_known(v_a_2061_, 1);
                    if v_isShared_2064_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2063_, 0, v_val_2065_);
                        v___x_2067_ = v___x_2063_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
                        v___x_2067_ = v_reuseFailAlloc_2068_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2063_);
                    crate::leanh::lean_dec(v_a_2061_);
                    crate::leanh::lean_inc(v_mvarId_2045_);
                    v___x_2069_ = l_Lean_MVarId_congrImplies_x3f(
                        v_mvarId_2045_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2069_) == 0 {
                        v_a_2070_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                        v_isSharedCheck_2081_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2069_)) as u8;
                        if v_isSharedCheck_2081_ == 0 {
                            v___x_2072_ = v___x_2069_;
                            v_isShared_2073_ = v_isSharedCheck_2081_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2070_);
                            crate::leanh::lean_dec(v___x_2069_);
                            v___x_2072_ = crate::leanh::lean_box(0);
                            v_isShared_2073_ = v_isSharedCheck_2081_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_2045_);
                        v_a_2082_ = crate::leanh::lean_ctor_get(v___x_2069_, 0);
                        v_isSharedCheck_2089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2069_)) as u8;
                        if v_isSharedCheck_2089_ == 0 {
                            v___x_2084_ = v___x_2069_;
                            v_isShared_2085_ = v_isSharedCheck_2089_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2082_);
                            crate::leanh::lean_dec(v___x_2069_);
                            v___x_2084_ = crate::leanh::lean_box(0);
                            v_isShared_2085_ = v_isSharedCheck_2089_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_2067_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_2070_) == 1 {
                    crate::leanh::lean_dec(v_mvarId_2045_);
                    v_val_2074_ = crate::leanh::lean_ctor_get(v_a_2070_, 0);
                    crate::leanh::lean_inc(v_val_2074_);
                    crate::leanh::lean_dec_ref_known(v_a_2070_, 1);
                    if v_isShared_2073_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2072_, 0, v_val_2074_);
                        v___x_2076_ = v___x_2072_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_val_2074_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2072_);
                    crate::leanh::lean_dec(v_a_2070_);
                    v___x_2078_ = l_Lean_MVarId_congr_x3f___closed__1;
                    v___x_2079_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__3_once),
                        _init_l_Lean_MVarId_congrCore___closed__3,
                    );
                    v___x_2080_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_2078_,
                        v_mvarId_2045_,
                        v___x_2079_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                    );
                    return v___x_2080_;
                }
            }
            6 => {
                return v___x_2076_;
            }
            7 => {
                if v_isShared_2085_ == 0 {
                    v___x_2087_ = v___x_2084_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2087_;
            }
            9 => {
                if v_isShared_2094_ == 0 {
                    v___x_2096_ = v___x_2093_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
                    v___x_2096_ = v_reuseFailAlloc_2097_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2096_;
            }
            11 => {
                if v_isShared_2103_ == 0 {
                    v___x_2105_ = v___x_2102_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
                    v___x_2105_ = v_reuseFailAlloc_2106_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_congrCore___boxed(
    mut v_mvarId_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ =
        l_Lean_MVarId_congrCore(v_mvarId_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
    crate::leanh::lean_dec(v_a_2112_);
    crate::leanh::lean_dec_ref(v_a_2111_);
    crate::leanh::lean_dec(v_a_2110_);
    crate::leanh::lean_dec_ref(v_a_2109_);
    return v_res_2114_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
    mut v_closePost_2115_: u8,
    mut v_mvarId_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_2130_: u8 = 0;
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v_val_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = l_Lean_Meta_Context_config(v_a_2118_);
                if v_closePost_2115_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2129_);
                    state = 1;
                    continue;
                } else {
                    v_transparency_2130_ = crate::leanh::lean_ctor_get_uint8(v___x_2129_, 9 as u32);
                    crate::leanh::lean_dec_ref(v___x_2129_);
                    v___x_2131_ = 2;
                    v___x_2132_ =
                        l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2130_, v___x_2131_);
                    if v___x_2132_ == 0 {
                        v___x_2133_ = 4;
                        v___x_2134_ = l_Lean_Meta_instBEqTransparencyMode_beq(
                            v_transparency_2130_,
                            v___x_2133_,
                        );
                        if v___x_2134_ == 0 {
                            v___x_2135_ = l_Lean_MVarId_congrPre(
                                v_mvarId_2116_,
                                v_a_2118_,
                                v_a_2119_,
                                v_a_2120_,
                                v_a_2121_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2135_) == 0 {
                                v_a_2136_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                                v_isSharedCheck_2152_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2135_)) as u8;
                                if v_isSharedCheck_2152_ == 0 {
                                    v___x_2138_ = v___x_2135_;
                                    v_isShared_2139_ = v_isSharedCheck_2152_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2136_);
                                    crate::leanh::lean_dec(v___x_2135_);
                                    v___x_2138_ = crate::leanh::lean_box(0);
                                    v_isShared_2139_ = v_isSharedCheck_2152_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                                v_isSharedCheck_2160_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2135_)) as u8;
                                if v_isSharedCheck_2160_ == 0 {
                                    v___x_2155_ = v___x_2135_;
                                    v_isShared_2156_ = v_isSharedCheck_2160_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2153_);
                                    crate::leanh::lean_dec(v___x_2135_);
                                    v___x_2155_ = crate::leanh::lean_box(0);
                                    v_isShared_2156_ = v_isSharedCheck_2160_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2124_ = lean_st_ref_take(v_a_2117_);
                v___x_2125_ = lean_array_push(v___x_2124_, v_mvarId_2116_);
                v___x_2126_ = lean_st_ref_set(v_a_2117_, v___x_2125_);
                v___x_2127_ = crate::leanh::lean_box(0);
                v___x_2128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2127_);
                return v___x_2128_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2136_) == 1 {
                    v_val_2140_ = crate::leanh::lean_ctor_get(v_a_2136_, 0);
                    crate::leanh::lean_inc(v_val_2140_);
                    crate::leanh::lean_dec_ref_known(v_a_2136_, 1);
                    v___x_2141_ = lean_st_ref_take(v_a_2117_);
                    v___x_2142_ = lean_array_push(v___x_2141_, v_val_2140_);
                    v___x_2143_ = lean_st_ref_set(v_a_2117_, v___x_2142_);
                    v___x_2144_ = crate::leanh::lean_box(0);
                    if v_isShared_2139_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2144_);
                        v___x_2146_ = v___x_2138_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
                        v___x_2146_ = v_reuseFailAlloc_2147_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2136_);
                    v___x_2148_ = crate::leanh::lean_box(0);
                    if v_isShared_2139_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2148_);
                        v___x_2150_ = v___x_2138_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
                        v___x_2150_ = v_reuseFailAlloc_2151_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2146_;
            }
            4 => {
                return v___x_2150_;
            }
            5 => {
                if v_isShared_2156_ == 0 {
                    v___x_2158_ = v___x_2155_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
                    v___x_2158_ = v_reuseFailAlloc_2159_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(
    mut v_closePost_2161_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
    mut v_a_2165_: *mut crate::leanh::LeanObject,
    mut v_a_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_closePost_boxed_2169_: u8 = 0;
    let mut v_res_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_closePost_boxed_2169_ = (crate::leanh::lean_unbox(v_closePost_2161_) as u8);
    v_res_2170_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
        v_closePost_boxed_2169_,
        v_mvarId_2162_,
        v_a_2163_,
        v_a_2164_,
        v_a_2165_,
        v_a_2166_,
        v_a_2167_,
    );
    crate::leanh::lean_dec(v_a_2167_);
    crate::leanh::lean_dec_ref(v_a_2166_);
    crate::leanh::lean_dec(v_a_2165_);
    crate::leanh::lean_dec_ref(v_a_2164_);
    crate::leanh::lean_dec(v_a_2163_);
    return v_res_2170_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0() -> u64
{
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: u64 = 0;
    v___x_2171_ = 2;
    v___x_2172_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2171_);
    return v___x_2172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(
    mut v_closePre_2173_: u8,
    mut v_closePost_2174_: u8,
    mut v_n_2175_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2176_: *mut crate::leanh::LeanObject,
    mut v_a_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
    mut v_a_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v_a_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_a_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2210_: u8 = 0;
    let mut v_ctxApprox_2211_: u8 = 0;
    let mut v_quasiPatternApprox_2212_: u8 = 0;
    let mut v_constApprox_2213_: u8 = 0;
    let mut v_isDefEqStuckEx_2214_: u8 = 0;
    let mut v_unificationHints_2215_: u8 = 0;
    let mut v_proofIrrelevance_2216_: u8 = 0;
    let mut v_assignSyntheticOpaque_2217_: u8 = 0;
    let mut v_offsetCnstrs_2218_: u8 = 0;
    let mut v_etaStruct_2219_: u8 = 0;
    let mut v_univApprox_2220_: u8 = 0;
    let mut v_iota_2221_: u8 = 0;
    let mut v_beta_2222_: u8 = 0;
    let mut v_proj_2223_: u8 = 0;
    let mut v_zeta_2224_: u8 = 0;
    let mut v_zetaDelta_2225_: u8 = 0;
    let mut v_zetaUnused_2226_: u8 = 0;
    let mut v_zetaHave_2227_: u8 = 0;
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v_trackZetaDelta_2231_: u8 = 0;
    let mut v_zetaDeltaSet_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2238_: u8 = 0;
    let mut v_inTypeClassResolution_2239_: u8 = 0;
    let mut v_cacheInferType_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut v_config_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u64 = 0;
    let mut v___x_2245_: u64 = 0;
    let mut v___x_2246_: u64 = 0;
    let mut v___x_2247_: u64 = 0;
    let mut v___x_2248_: u64 = 0;
    let mut v_key_2249_: u64 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_reuseFailAlloc_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_closePre_2173_ == 0 {
                    v_val_2184_ = v_mvarId_2176_;
                    state = 1;
                    continue;
                } else {
                    v___x_2209_ = l_Lean_Meta_Context_config(v_a_2178_);
                    v_foApprox_2210_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 0 as u32);
                    v_ctxApprox_2211_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 1 as u32);
                    v_quasiPatternApprox_2212_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2209_, 2 as u32);
                    v_constApprox_2213_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 3 as u32);
                    v_isDefEqStuckEx_2214_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2209_, 4 as u32);
                    v_unificationHints_2215_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2209_, 5 as u32);
                    v_proofIrrelevance_2216_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2209_, 6 as u32);
                    v_assignSyntheticOpaque_2217_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2209_, 7 as u32);
                    v_offsetCnstrs_2218_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 8 as u32);
                    v_etaStruct_2219_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 10 as u32);
                    v_univApprox_2220_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 11 as u32);
                    v_iota_2221_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 12 as u32);
                    v_beta_2222_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 13 as u32);
                    v_proj_2223_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 14 as u32);
                    v_zeta_2224_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 15 as u32);
                    v_zetaDelta_2225_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 16 as u32);
                    v_zetaUnused_2226_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 17 as u32);
                    v_zetaHave_2227_ = crate::leanh::lean_ctor_get_uint8(v___x_2209_, 18 as u32);
                    v_isSharedCheck_2264_ = (!crate::leanh::lean_is_exclusive(v___x_2209_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2229_ = v___x_2209_;
                        v_isShared_2230_ = v_isSharedCheck_2264_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2209_);
                        v___x_2229_ = crate::leanh::lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2264_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_2185_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2186_ = lean_nat_dec_eq(v_n_2175_, v_zero_2185_);
                if v_isZero_2186_ == 1 {
                    v___x_2187_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
                        v_closePost_2174_,
                        v_val_2184_,
                        v_a_2177_,
                        v_a_2178_,
                        v_a_2179_,
                        v_a_2180_,
                        v_a_2181_,
                    );
                    return v___x_2187_;
                } else {
                    crate::leanh::lean_inc(v_val_2184_);
                    v___x_2188_ = crate::leanh::lean_alloc_closure(
                        l_Lean_MVarId_congrCore___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_2188_, 0, v_val_2184_);
                    v___x_2189_ =
                        l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
                            v___x_2188_,
                            v_a_2178_,
                            v_a_2179_,
                            v_a_2180_,
                            v_a_2181_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2189_) == 0 {
                        v_a_2190_ = crate::leanh::lean_ctor_get(v___x_2189_, 0);
                        crate::leanh::lean_inc(v_a_2190_);
                        crate::leanh::lean_dec_ref_known(v___x_2189_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2190_) == 1 {
                            crate::leanh::lean_dec(v_val_2184_);
                            v_val_2191_ = crate::leanh::lean_ctor_get(v_a_2190_, 0);
                            crate::leanh::lean_inc(v_val_2191_);
                            crate::leanh::lean_dec_ref_known(v_a_2190_, 1);
                            v_one_2192_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_n_2193_ = lean_nat_sub(v_n_2175_, v_one_2192_);
                            v___x_2194_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_2173_, v_closePost_2174_, v_n_2193_, v_val_2191_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
                            crate::leanh::lean_dec(v_n_2193_);
                            return v___x_2194_;
                        } else {
                            crate::leanh::lean_dec(v_a_2190_);
                            v___x_2195_ =
                                l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
                                    v_closePost_2174_,
                                    v_val_2184_,
                                    v_a_2177_,
                                    v_a_2178_,
                                    v_a_2179_,
                                    v_a_2180_,
                                    v_a_2181_,
                                );
                            return v___x_2195_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2184_);
                        v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2189_, 0);
                        v_isSharedCheck_2203_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2189_)) as u8;
                        if v_isSharedCheck_2203_ == 0 {
                            v___x_2198_ = v___x_2189_;
                            v_isShared_2199_ = v_isSharedCheck_2203_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2196_);
                            crate::leanh::lean_dec(v___x_2189_);
                            v___x_2198_ = crate::leanh::lean_box(0);
                            v_isShared_2199_ = v_isSharedCheck_2203_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2199_ == 0 {
                    v___x_2201_ = v___x_2198_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2201_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2205_) == 1 {
                    v_val_2206_ = crate::leanh::lean_ctor_get(v_a_2205_, 0);
                    crate::leanh::lean_inc(v_val_2206_);
                    crate::leanh::lean_dec_ref_known(v_a_2205_, 1);
                    v_val_2184_ = v_val_2206_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_2205_);
                    v___x_2207_ = crate::leanh::lean_box(0);
                    v___x_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2208_, 0, v___x_2207_);
                    return v___x_2208_;
                }
            }
            5 => {
                v_trackZetaDelta_2231_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2232_ = crate::leanh::lean_ctor_get(v_a_2178_, 1);
                v_lctx_2233_ = crate::leanh::lean_ctor_get(v_a_2178_, 2);
                v_localInstances_2234_ = crate::leanh::lean_ctor_get(v_a_2178_, 3);
                v_defEqCtx_x3f_2235_ = crate::leanh::lean_ctor_get(v_a_2178_, 4);
                v_synthPendingDepth_2236_ = crate::leanh::lean_ctor_get(v_a_2178_, 5);
                v_canUnfold_x3f_2237_ = crate::leanh::lean_ctor_get(v_a_2178_, 6);
                v_univApprox_2238_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2239_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2240_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2241_ = 2;
                if v_isShared_2230_ == 0 {
                    v_config_2243_ = v___x_2229_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        0 as u32,
                        v_foApprox_2210_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        1 as u32,
                        v_ctxApprox_2211_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        2 as u32,
                        v_quasiPatternApprox_2212_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        3 as u32,
                        v_constApprox_2213_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        4 as u32,
                        v_isDefEqStuckEx_2214_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        5 as u32,
                        v_unificationHints_2215_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        6 as u32,
                        v_proofIrrelevance_2216_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        7 as u32,
                        v_assignSyntheticOpaque_2217_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        8 as u32,
                        v_offsetCnstrs_2218_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        10 as u32,
                        v_etaStruct_2219_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        11 as u32,
                        v_univApprox_2220_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        12 as u32,
                        v_iota_2221_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        13 as u32,
                        v_beta_2222_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        14 as u32,
                        v_proj_2223_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        15 as u32,
                        v_zeta_2224_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        16 as u32,
                        v_zetaDelta_2225_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        17 as u32,
                        v_zetaUnused_2226_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        18 as u32,
                        v_zetaHave_2227_,
                    );
                    v_config_2243_ = v_reuseFailAlloc_2263_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2243_, 9 as u32, v___x_2241_);
                v___x_2244_ = l_Lean_Meta_Context_configKey(v_a_2178_);
                v___x_2245_ = 3u64;
                v___x_2246_ = lean_uint64_shift_right(v___x_2244_, v___x_2245_);
                v___x_2247_ = lean_uint64_shift_left(v___x_2246_, v___x_2245_);
                v___x_2248_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0);
                v_key_2249_ = lean_uint64_lor(v___x_2247_, v___x_2248_);
                v___x_2250_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2250_, 0, v_config_2243_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2250_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2249_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2237_);
                crate::leanh::lean_inc(v_synthPendingDepth_2236_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2235_);
                crate::leanh::lean_inc_ref(v_localInstances_2234_);
                crate::leanh::lean_inc_ref(v_lctx_2233_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2232_);
                v___x_2251_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                crate::leanh::lean_ctor_set(v___x_2251_, 1, v_zetaDeltaSet_2232_);
                crate::leanh::lean_ctor_set(v___x_2251_, 2, v_lctx_2233_);
                crate::leanh::lean_ctor_set(v___x_2251_, 3, v_localInstances_2234_);
                crate::leanh::lean_ctor_set(v___x_2251_, 4, v_defEqCtx_x3f_2235_);
                crate::leanh::lean_ctor_set(v___x_2251_, 5, v_synthPendingDepth_2236_);
                crate::leanh::lean_ctor_set(v___x_2251_, 6, v_canUnfold_x3f_2237_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2231_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2238_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2239_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2240_,
                );
                v___x_2252_ = l_Lean_MVarId_congrPre(
                    v_mvarId_2176_,
                    v___x_2251_,
                    v_a_2179_,
                    v_a_2180_,
                    v_a_2181_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2251_, 7);
                if crate::leanh::lean_obj_tag(v___x_2252_) == 0 {
                    v_a_2253_ = crate::leanh::lean_ctor_get(v___x_2252_, 0);
                    crate::leanh::lean_inc(v_a_2253_);
                    crate::leanh::lean_dec_ref_known(v___x_2252_, 1);
                    v_a_2205_ = v_a_2253_;
                    state = 4;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___x_2252_) == 0 {
                        v_a_2254_ = crate::leanh::lean_ctor_get(v___x_2252_, 0);
                        crate::leanh::lean_inc(v_a_2254_);
                        crate::leanh::lean_dec_ref_known(v___x_2252_, 1);
                        v_a_2205_ = v_a_2254_;
                        state = 4;
                        continue;
                    } else {
                        v_a_2255_ = crate::leanh::lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2262_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2262_ == 0 {
                            v___x_2257_ = v___x_2252_;
                            v_isShared_2258_ = v_isSharedCheck_2262_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2255_);
                            crate::leanh::lean_dec(v___x_2252_);
                            v___x_2257_ = crate::leanh::lean_box(0);
                            v_isShared_2258_ = v_isSharedCheck_2262_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_2258_ == 0 {
                    v___x_2260_ = v___x_2257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
                    v___x_2260_ = v_reuseFailAlloc_2261_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(
    mut v_closePre_2265_: u8,
    mut v_closePost_2266_: u8,
    mut v_n_2267_: *mut crate::leanh::LeanObject,
    mut v_as_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_2268_) == 0 {
                    v___x_2275_ = crate::leanh::lean_box(0);
                    v___x_2276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
                    return v___x_2276_;
                } else {
                    v_head_2277_ = crate::leanh::lean_ctor_get(v_as_2268_, 0);
                    crate::leanh::lean_inc(v_head_2277_);
                    v_tail_2278_ = crate::leanh::lean_ctor_get(v_as_2268_, 1);
                    crate::leanh::lean_inc(v_tail_2278_);
                    crate::leanh::lean_dec_ref_known(v_as_2268_, 2);
                    v___x_2279_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(
                        v_closePre_2265_,
                        v_closePost_2266_,
                        v_n_2267_,
                        v_head_2277_,
                        v___y_2269_,
                        v___y_2270_,
                        v___y_2271_,
                        v___y_2272_,
                        v___y_2273_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2279_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2279_, 1);
                        v_as_2268_ = v_tail_2278_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_2278_);
                        return v___x_2279_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(
    mut v_closePre_2281_: *mut crate::leanh::LeanObject,
    mut v_closePost_2282_: *mut crate::leanh::LeanObject,
    mut v_n_2283_: *mut crate::leanh::LeanObject,
    mut v_as_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_closePre_boxed_2291_: u8 = 0;
    let mut v_closePost_boxed_2292_: u8 = 0;
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2291_ = (crate::leanh::lean_unbox(v_closePre_2281_) as u8);
    v_closePost_boxed_2292_ = (crate::leanh::lean_unbox(v_closePost_2282_) as u8);
    v_res_2293_ =
        l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(
            v_closePre_boxed_2291_,
            v_closePost_boxed_2292_,
            v_n_2283_,
            v_as_2284_,
            v___y_2285_,
            v___y_2286_,
            v___y_2287_,
            v___y_2288_,
            v___y_2289_,
        );
    crate::leanh::lean_dec(v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2288_);
    crate::leanh::lean_dec(v___y_2287_);
    crate::leanh::lean_dec_ref(v___y_2286_);
    crate::leanh::lean_dec(v___y_2285_);
    crate::leanh::lean_dec(v_n_2283_);
    return v_res_2293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(
    mut v_closePre_2294_: *mut crate::leanh::LeanObject,
    mut v_closePost_2295_: *mut crate::leanh::LeanObject,
    mut v_n_2296_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_a_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_closePre_boxed_2304_: u8 = 0;
    let mut v_closePost_boxed_2305_: u8 = 0;
    let mut v_res_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2304_ = (crate::leanh::lean_unbox(v_closePre_2294_) as u8);
    v_closePost_boxed_2305_ = (crate::leanh::lean_unbox(v_closePost_2295_) as u8);
    v_res_2306_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(
        v_closePre_boxed_2304_,
        v_closePost_boxed_2305_,
        v_n_2296_,
        v_mvarId_2297_,
        v_a_2298_,
        v_a_2299_,
        v_a_2300_,
        v_a_2301_,
        v_a_2302_,
    );
    crate::leanh::lean_dec(v_a_2302_);
    crate::leanh::lean_dec_ref(v_a_2301_);
    crate::leanh::lean_dec(v_a_2300_);
    crate::leanh::lean_dec_ref(v_a_2299_);
    crate::leanh::lean_dec(v_a_2298_);
    crate::leanh::lean_dec(v_n_2296_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_MVarId_congrN(
    mut v_mvarId_2309_: *mut crate::leanh::LeanObject,
    mut v_depth_2310_: *mut crate::leanh::LeanObject,
    mut v_closePre_2311_: u8,
    mut v_closePost_2312_: u8,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
    mut v_a_2315_: *mut crate::leanh::LeanObject,
    mut v_a_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_unused_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2318_ = l_Lean_MVarId_congrN___closed__0;
                v___x_2319_ = lean_st_mk_ref(v___x_2318_);
                v___x_2320_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(
                    v_closePre_2311_,
                    v_closePost_2312_,
                    v_depth_2310_,
                    v_mvarId_2309_,
                    v___x_2319_,
                    v_a_2313_,
                    v_a_2314_,
                    v_a_2315_,
                    v_a_2316_,
                );
                if crate::leanh::lean_obj_tag(v___x_2320_) == 0 {
                    v_isSharedCheck_2329_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v_unused_2330_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                        crate::leanh::lean_dec(v_unused_2330_);
                        v___x_2322_ = v___x_2320_;
                        v_isShared_2323_ = v_isSharedCheck_2329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2320_);
                        v___x_2322_ = crate::leanh::lean_box(0);
                        v_isShared_2323_ = v_isSharedCheck_2329_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2319_);
                    v_a_2331_ = crate::leanh::lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2338_ = (!crate::leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2338_ == 0 {
                        v___x_2333_ = v___x_2320_;
                        v_isShared_2334_ = v_isSharedCheck_2338_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2331_);
                        crate::leanh::lean_dec(v___x_2320_);
                        v___x_2333_ = crate::leanh::lean_box(0);
                        v_isShared_2334_ = v_isSharedCheck_2338_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2324_ = lean_st_ref_get(v___x_2319_);
                crate::leanh::lean_dec(v___x_2319_);
                v___x_2325_ = lean_array_to_list(v___x_2324_);
                if v_isShared_2323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2322_, 0, v___x_2325_);
                    v___x_2327_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
                    v___x_2327_ = v_reuseFailAlloc_2328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2327_;
            }
            3 => {
                if v_isShared_2334_ == 0 {
                    v___x_2336_ = v___x_2333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
                    v___x_2336_ = v_reuseFailAlloc_2337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_congrN___boxed(
    mut v_mvarId_2339_: *mut crate::leanh::LeanObject,
    mut v_depth_2340_: *mut crate::leanh::LeanObject,
    mut v_closePre_2341_: *mut crate::leanh::LeanObject,
    mut v_closePost_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_closePre_boxed_2348_: u8 = 0;
    let mut v_closePost_boxed_2349_: u8 = 0;
    let mut v_res_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2348_ = (crate::leanh::lean_unbox(v_closePre_2341_) as u8);
    v_closePost_boxed_2349_ = (crate::leanh::lean_unbox(v_closePost_2342_) as u8);
    v_res_2350_ = l_Lean_MVarId_congrN(
        v_mvarId_2339_,
        v_depth_2340_,
        v_closePre_boxed_2348_,
        v_closePost_boxed_2349_,
        v_a_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
    );
    crate::leanh::lean_dec(v_a_2346_);
    crate::leanh::lean_dec_ref(v_a_2345_);
    crate::leanh::lean_dec(v_a_2344_);
    crate::leanh::lean_dec_ref(v_a_2343_);
    crate::leanh::lean_dec(v_depth_2340_);
    return v_res_2350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Congr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Congr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Congr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_CongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Congr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Congr(builtin);
}
