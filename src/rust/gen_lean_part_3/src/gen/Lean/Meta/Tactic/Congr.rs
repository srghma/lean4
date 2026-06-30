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
    m_data: [104, 95, 99, 111, 110, 103, 114, 95, 116, 104, 109, 0],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0_value
        ) as *mut leanh::LeanObject,
        15603447039181438785 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777216 as *mut leanh::LeanObject],
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___lam__0___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
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
static mut l_Lean_MVarId_congr_x3f___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            16122875713692181903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congr_x3f___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [99, 111, 110, 103, 114, 0],
    };
static mut l_Lean_MVarId_congr_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congr_x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11699215918282396216 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congr_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congr_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
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
static mut l_Lean_MVarId_hcongr_x3f___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            13589827700912665667 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_hcongr_x3f___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_hcongr_x3f___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
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
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value:
    leanh::LeanStringObject<61> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_congrImplies_x3f___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
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
            105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_MVarId_congrImplies_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congrImplies_x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            11074994739801900941 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congrImplies_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrImplies_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congrCore___closed__0_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
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
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 99, 111, 110,
            103, 114, 117, 101, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_MVarId_congrCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_MVarId_congrCore___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_congrCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrCore___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_MVarId_congrCore___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrCore___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_congrCore___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_congrCore___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0: u64 = 0;
pub static l_Lean_MVarId_congrN___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_MVarId_congrN___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_congrN___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_congrPre(
    mut v_mvarId_1176_: *mut leanh::LeanObject,
    mut v_a_1177_: *mut leanh::LeanObject,
    mut v_a_1178_: *mut leanh::LeanObject,
    mut v_a_1179_: *mut leanh::LeanObject,
    mut v_a_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___y_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: u8 = 0;
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1204_: u8 = 0;
    let mut v_a_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1220_: u8 = 0;
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut v_unused_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___y_1232_: u8 = 0;
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut v_unused_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    let mut v___x_1250_: u8 = 0;
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_a_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1256_: u8 = 0;
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1182_) == 0 {
                    v_a_1183_ = leanh::lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1252_ = (!leanh::lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1252_ == 0 {
                        v___x_1185_ = v___x_1182_;
                        v_isShared_1186_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1183_);
                        leanh::lean_dec(v___x_1182_);
                        v___x_1185_ = leanh::lean_box(0);
                        v_isShared_1186_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1253_ = leanh::lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1260_ = (!leanh::lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1260_ == 0 {
                        v___x_1255_ = v___x_1182_;
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1253_);
                        leanh::lean_dec(v___x_1182_);
                        v___x_1255_ = leanh::lean_box(0);
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1216_ = 1;
                leanh::lean_inc(v_a_1183_);
                v___x_1217_ = l_Lean_MVarId_refl(
                    v_a_1183_,
                    v___x_1216_,
                    v_a_1177_,
                    v_a_1178_,
                    v_a_1179_,
                    v_a_1180_,
                );
                if leanh::lean_obj_tag(v___x_1217_) == 0 {
                    leanh::lean_del_object(v___x_1185_);
                    leanh::lean_dec(v_a_1183_);
                    v_isSharedCheck_1225_ = (!leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v_unused_1226_ = leanh::lean_ctor_get(v___x_1217_, 0);
                        leanh::lean_dec(v_unused_1226_);
                        v___x_1219_ = v___x_1217_;
                        v_isShared_1220_ = v_isSharedCheck_1225_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1217_);
                        v___x_1219_ = leanh::lean_box(0);
                        v_isShared_1220_ = v_isSharedCheck_1225_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_1227_ = leanh::lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1251_ = (!leanh::lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1229_ = v___x_1217_;
                        v_isShared_1230_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1227_);
                        leanh::lean_dec(v___x_1217_);
                        v___x_1229_ = leanh::lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1251_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_1189_ == 0 {
                    leanh::lean_dec_ref(v___y_1188_);
                    leanh::lean_del_object(v___x_1185_);
                    leanh::lean_inc(v_a_1183_);
                    v___x_1190_ = l_Lean_MVarId_assumptionCore(
                        v_a_1183_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_,
                    );
                    if leanh::lean_obj_tag(v___x_1190_) == 0 {
                        v_a_1191_ = leanh::lean_ctor_get(v___x_1190_, 0);
                        v_isSharedCheck_1204_ =
                            (!leanh::lean_is_exclusive(v___x_1190_)) as u8;
                        if v_isSharedCheck_1204_ == 0 {
                            v___x_1193_ = v___x_1190_;
                            v_isShared_1194_ = v_isSharedCheck_1204_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1191_);
                            leanh::lean_dec(v___x_1190_);
                            v___x_1193_ = leanh::lean_box(0);
                            v_isShared_1194_ = v_isSharedCheck_1204_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1183_);
                        v_a_1205_ = leanh::lean_ctor_get(v___x_1190_, 0);
                        v_isSharedCheck_1212_ =
                            (!leanh::lean_is_exclusive(v___x_1190_)) as u8;
                        if v_isSharedCheck_1212_ == 0 {
                            v___x_1207_ = v___x_1190_;
                            v_isShared_1208_ = v_isSharedCheck_1212_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1205_);
                            leanh::lean_dec(v___x_1190_);
                            v___x_1207_ = leanh::lean_box(0);
                            v_isShared_1208_ = v_isSharedCheck_1212_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1183_);
                    if v_isShared_1186_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1185_, 1);
                        leanh::lean_ctor_set(v___x_1185_, 0, v___y_1188_);
                        v___x_1214_ = v___x_1185_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1215_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___y_1188_);
                        v___x_1214_ = v_reuseFailAlloc_1215_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1195_ = (leanh::lean_unbox(v_a_1191_) as u8);
                leanh::lean_dec(v_a_1191_);
                if v___x_1195_ == 0 {
                    v___x_1196_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1196_, 0, v_a_1183_);
                    if v_isShared_1194_ == 0 {
                        leanh::lean_ctor_set(v___x_1193_, 0, v___x_1196_);
                        v___x_1198_ = v___x_1193_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
                        v___x_1198_ = v_reuseFailAlloc_1199_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1183_);
                    v___x_1200_ = leanh::lean_box(0);
                    if v_isShared_1194_ == 0 {
                        leanh::lean_ctor_set(v___x_1193_, 0, v___x_1200_);
                        v___x_1202_ = v___x_1193_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1203_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
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
                    v_reuseFailAlloc_1211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
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
                v___x_1221_ = leanh::lean_box(0);
                if v_isShared_1220_ == 0 {
                    leanh::lean_ctor_set(v___x_1219_, 0, v___x_1221_);
                    v___x_1223_ = v___x_1219_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
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
                    leanh::lean_inc(v_a_1227_);
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
                    leanh::lean_del_object(v___x_1229_);
                    leanh::lean_dec(v_a_1227_);
                    leanh::lean_inc(v_a_1183_);
                    v___x_1233_ =
                        l_Lean_MVarId_hrefl(v_a_1183_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
                    if leanh::lean_obj_tag(v___x_1233_) == 0 {
                        leanh::lean_del_object(v___x_1185_);
                        leanh::lean_dec(v_a_1183_);
                        v_isSharedCheck_1241_ =
                            (!leanh::lean_is_exclusive(v___x_1233_)) as u8;
                        if v_isSharedCheck_1241_ == 0 {
                            v_unused_1242_ = leanh::lean_ctor_get(v___x_1233_, 0);
                            leanh::lean_dec(v_unused_1242_);
                            v___x_1235_ = v___x_1233_;
                            v_isShared_1236_ = v_isSharedCheck_1241_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1233_);
                            v___x_1235_ = leanh::lean_box(0);
                            v_isShared_1236_ = v_isSharedCheck_1241_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_1243_ = leanh::lean_ctor_get(v___x_1233_, 0);
                        leanh::lean_inc(v_a_1243_);
                        leanh::lean_dec_ref_known(v___x_1233_, 1);
                        v___x_1244_ = l_Lean_Exception_isInterrupt(v_a_1243_);
                        if v___x_1244_ == 0 {
                            leanh::lean_inc(v_a_1243_);
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
                    leanh::lean_del_object(v___x_1185_);
                    leanh::lean_dec(v_a_1183_);
                    if v_isShared_1230_ == 0 {
                        v___x_1247_ = v___x_1229_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_1248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1227_);
                        v___x_1247_ = v_reuseFailAlloc_1248_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1237_ = leanh::lean_box(0);
                if v_isShared_1236_ == 0 {
                    leanh::lean_ctor_set(v___x_1235_, 0, v___x_1237_);
                    v___x_1239_ = v___x_1235_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
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
                    v_reuseFailAlloc_1259_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
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
    mut v_mvarId_1261_: *mut leanh::LeanObject,
    mut v_a_1262_: *mut leanh::LeanObject,
    mut v_a_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
    mut v_a_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ =
        l_Lean_MVarId_congrPre(v_mvarId_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
    leanh::lean_dec(v_a_1265_);
    leanh::lean_dec_ref(v_a_1264_);
    leanh::lean_dec(v_a_1263_);
    leanh::lean_dec_ref(v_a_1262_);
    return v_res_1267_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(
    mut v_fst_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_x_1270_: *mut leanh::LeanObject,
    mut v___y_1271_: *mut leanh::LeanObject,
    mut v___y_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1269_) == 0 {
                    leanh::lean_dec(v_fst_1268_);
                    v___x_1276_ = l_List_reverse___redArg(v_x_1270_);
                    v___x_1277_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1277_, 0, v___x_1276_);
                    return v___x_1277_;
                } else {
                    v_head_1278_ = leanh::lean_ctor_get(v_x_1269_, 0);
                    v_tail_1279_ = leanh::lean_ctor_get(v_x_1269_, 1);
                    v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v_x_1269_)) as u8;
                    if v_isSharedCheck_1297_ == 0 {
                        v___x_1281_ = v_x_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1279_);
                        leanh::lean_inc(v_head_1278_);
                        leanh::lean_dec(v_x_1269_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1297_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_fst_1268_);
                v___x_1283_ = l_Lean_MVarId_tryClear(
                    v_head_1278_,
                    v_fst_1268_,
                    v___y_1271_,
                    v___y_1272_,
                    v___y_1273_,
                    v___y_1274_,
                );
                if leanh::lean_obj_tag(v___x_1283_) == 0 {
                    v_a_1284_ = leanh::lean_ctor_get(v___x_1283_, 0);
                    leanh::lean_inc(v_a_1284_);
                    leanh::lean_dec_ref_known(v___x_1283_, 1);
                    if v_isShared_1282_ == 0 {
                        leanh::lean_ctor_set(v___x_1281_, 1, v_x_1270_);
                        leanh::lean_ctor_set(v___x_1281_, 0, v_a_1284_);
                        v___x_1286_ = v___x_1281_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1288_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1284_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_x_1270_);
                        v___x_1286_ = v_reuseFailAlloc_1288_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1281_);
                    leanh::lean_dec(v_tail_1279_);
                    leanh::lean_dec(v_x_1270_);
                    leanh::lean_dec(v_fst_1268_);
                    v_a_1289_ = leanh::lean_ctor_get(v___x_1283_, 0);
                    v_isSharedCheck_1296_ = (!leanh::lean_is_exclusive(v___x_1283_)) as u8;
                    if v_isSharedCheck_1296_ == 0 {
                        v___x_1291_ = v___x_1283_;
                        v_isShared_1292_ = v_isSharedCheck_1296_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1289_);
                        leanh::lean_dec(v___x_1283_);
                        v___x_1291_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
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
    mut v_fst_1298_: *mut leanh::LeanObject,
    mut v_x_1299_: *mut leanh::LeanObject,
    mut v_x_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_1298_, v_x_1299_, v_x_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
    leanh::lean_dec(v___y_1304_);
    leanh::lean_dec_ref(v___y_1303_);
    leanh::lean_dec(v___y_1302_);
    leanh::lean_dec_ref(v___y_1301_);
    return v_res_1306_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
    mut v_mvarId_1314_: *mut leanh::LeanObject,
    mut v_congrThm_1315_: *mut leanh::LeanObject,
    mut v_a_1316_: *mut leanh::LeanObject,
    mut v_a_1317_: *mut leanh::LeanObject,
    mut v_a_1318_: *mut leanh::LeanObject,
    mut v_a_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1347_: u8 = 0;
    let mut v_a_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_a_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ =
                    l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1;
                v___x_1322_ = l_Lean_Core_mkFreshUserName(v___x_1321_, v_a_1318_, v_a_1319_);
                if leanh::lean_obj_tag(v___x_1322_) == 0 {
                    v_a_1323_ = leanh::lean_ctor_get(v___x_1322_, 0);
                    leanh::lean_inc(v_a_1323_);
                    leanh::lean_dec_ref_known(v___x_1322_, 1);
                    v_type_1324_ = leanh::lean_ctor_get(v_congrThm_1315_, 0);
                    leanh::lean_inc_ref(v_type_1324_);
                    v_proof_1325_ = leanh::lean_ctor_get(v_congrThm_1315_, 1);
                    leanh::lean_inc_ref(v_proof_1325_);
                    leanh::lean_dec_ref(v_congrThm_1315_);
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
                    if leanh::lean_obj_tag(v___x_1326_) == 0 {
                        v_a_1327_ = leanh::lean_ctor_get(v___x_1326_, 0);
                        leanh::lean_inc(v_a_1327_);
                        leanh::lean_dec_ref_known(v___x_1326_, 1);
                        v___x_1328_ = 1;
                        v___x_1329_ = l_Lean_Meta_intro1Core(
                            v_a_1327_,
                            v___x_1328_,
                            v_a_1316_,
                            v_a_1317_,
                            v_a_1318_,
                            v_a_1319_,
                        );
                        if leanh::lean_obj_tag(v___x_1329_) == 0 {
                            v_a_1330_ = leanh::lean_ctor_get(v___x_1329_, 0);
                            leanh::lean_inc(v_a_1330_);
                            leanh::lean_dec_ref_known(v___x_1329_, 1);
                            v_fst_1331_ = leanh::lean_ctor_get(v_a_1330_, 0);
                            leanh::lean_inc_n(v_fst_1331_, 2);
                            v_snd_1332_ = leanh::lean_ctor_get(v_a_1330_, 1);
                            leanh::lean_inc(v_snd_1332_);
                            leanh::lean_dec(v_a_1330_);
                            v___x_1333_ = l_Lean_mkFVar(v_fst_1331_);
                            v___x_1334_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2;
                            v___x_1335_ = leanh::lean_box(0);
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
                            if leanh::lean_obj_tag(v___x_1336_) == 0 {
                                v_a_1337_ = leanh::lean_ctor_get(v___x_1336_, 0);
                                leanh::lean_inc(v_a_1337_);
                                leanh::lean_dec_ref_known(v___x_1336_, 1);
                                v___x_1338_ = leanh::lean_box(0);
                                v___x_1339_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(v_fst_1331_, v_a_1337_, v___x_1338_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
                                return v___x_1339_;
                            } else {
                                leanh::lean_dec(v_fst_1331_);
                                return v___x_1336_;
                            }
                        } else {
                            v_a_1340_ = leanh::lean_ctor_get(v___x_1329_, 0);
                            v_isSharedCheck_1347_ =
                                (!leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1347_ == 0 {
                                v___x_1342_ = v___x_1329_;
                                v_isShared_1343_ = v_isSharedCheck_1347_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1340_);
                                leanh::lean_dec(v___x_1329_);
                                v___x_1342_ = leanh::lean_box(0);
                                v_isShared_1343_ = v_isSharedCheck_1347_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1348_ = leanh::lean_ctor_get(v___x_1326_, 0);
                        v_isSharedCheck_1355_ =
                            (!leanh::lean_is_exclusive(v___x_1326_)) as u8;
                        if v_isSharedCheck_1355_ == 0 {
                            v___x_1350_ = v___x_1326_;
                            v_isShared_1351_ = v_isSharedCheck_1355_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1348_);
                            leanh::lean_dec(v___x_1326_);
                            v___x_1350_ = leanh::lean_box(0);
                            v_isShared_1351_ = v_isSharedCheck_1355_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_congrThm_1315_);
                    leanh::lean_dec(v_mvarId_1314_);
                    v_a_1356_ = leanh::lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1363_ = (!leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1363_ == 0 {
                        v___x_1358_ = v___x_1322_;
                        v_isShared_1359_ = v_isSharedCheck_1363_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1356_);
                        leanh::lean_dec(v___x_1322_);
                        v___x_1358_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
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
                    v_reuseFailAlloc_1354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
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
                    v_reuseFailAlloc_1362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
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
    mut v_mvarId_1364_: *mut leanh::LeanObject,
    mut v_congrThm_1365_: *mut leanh::LeanObject,
    mut v_a_1366_: *mut leanh::LeanObject,
    mut v_a_1367_: *mut leanh::LeanObject,
    mut v_a_1368_: *mut leanh::LeanObject,
    mut v_a_1369_: *mut leanh::LeanObject,
    mut v_a_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1371_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
        v_mvarId_1364_,
        v_congrThm_1365_,
        v_a_1366_,
        v_a_1367_,
        v_a_1368_,
        v_a_1369_,
    );
    leanh::lean_dec(v_a_1369_);
    leanh::lean_dec_ref(v_a_1368_);
    leanh::lean_dec(v_a_1367_);
    leanh::lean_dec_ref(v_a_1366_);
    return v_res_1371_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
    mut v_mvarId_1372_: *mut leanh::LeanObject,
    mut v_x_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
    mut v___y_1375_: *mut leanh::LeanObject,
    mut v___y_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1383_: u8 = 0;
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_a_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1372_,
                    v_x_1373_,
                    v___y_1374_,
                    v___y_1375_,
                    v___y_1376_,
                    v___y_1377_,
                );
                if leanh::lean_obj_tag(v___x_1379_) == 0 {
                    v_a_1380_ = leanh::lean_ctor_get(v___x_1379_, 0);
                    v_isSharedCheck_1387_ = (!leanh::lean_is_exclusive(v___x_1379_)) as u8;
                    if v_isSharedCheck_1387_ == 0 {
                        v___x_1382_ = v___x_1379_;
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1380_);
                        leanh::lean_dec(v___x_1379_);
                        v___x_1382_ = leanh::lean_box(0);
                        v_isShared_1383_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1388_ = leanh::lean_ctor_get(v___x_1379_, 0);
                    v_isSharedCheck_1395_ = (!leanh::lean_is_exclusive(v___x_1379_)) as u8;
                    if v_isSharedCheck_1395_ == 0 {
                        v___x_1390_ = v___x_1379_;
                        v_isShared_1391_ = v_isSharedCheck_1395_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1388_);
                        leanh::lean_dec(v___x_1379_);
                        v___x_1390_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
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
                    v_reuseFailAlloc_1394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
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
    mut v_mvarId_1396_: *mut leanh::LeanObject,
    mut v_x_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(
        v_mvarId_1396_,
        v_x_1397_,
        v___y_1398_,
        v___y_1399_,
        v___y_1400_,
        v___y_1401_,
    );
    leanh::lean_dec(v___y_1401_);
    leanh::lean_dec_ref(v___y_1400_);
    leanh::lean_dec(v___y_1399_);
    leanh::lean_dec_ref(v___y_1398_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(
    mut v_00_u03b1_1404_: *mut leanh::LeanObject,
    mut v_mvarId_1405_: *mut leanh::LeanObject,
    mut v_x_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1413_: *mut leanh::LeanObject,
    mut v_mvarId_1414_: *mut leanh::LeanObject,
    mut v_x_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1(
        v_00_u03b1_1413_,
        v_mvarId_1414_,
        v_x_1415_,
        v___y_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
    );
    leanh::lean_dec(v___y_1419_);
    leanh::lean_dec_ref(v___y_1418_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_Lean_MVarId_congr_x3f___lam__0(
    mut v_mvarId_1425_: *mut leanh::LeanObject,
    mut v___x_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1437_: u8 = 0;
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u8 = 0;
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v_val_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_a_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1481_: u8 = 0;
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1485_: u8 = 0;
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1491_: u8 = 0;
    let mut v_a_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1499_: u8 = 0;
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut v_a_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_a_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1512_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1425_);
                v___x_1432_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1425_,
                    v___x_1426_,
                    v___y_1427_,
                    v___y_1428_,
                    v___y_1429_,
                    v___y_1430_,
                );
                if leanh::lean_obj_tag(v___x_1432_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1432_, 1);
                    leanh::lean_inc(v_mvarId_1425_);
                    v___x_1433_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_1425_,
                        v___y_1427_,
                        v___y_1428_,
                        v___y_1429_,
                        v___y_1430_,
                    );
                    if leanh::lean_obj_tag(v___x_1433_) == 0 {
                        v_a_1434_ = leanh::lean_ctor_get(v___x_1433_, 0);
                        v_isSharedCheck_1500_ =
                            (!leanh::lean_is_exclusive(v___x_1433_)) as u8;
                        if v_isSharedCheck_1500_ == 0 {
                            v___x_1436_ = v___x_1433_;
                            v_isShared_1437_ = v_isSharedCheck_1500_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1434_);
                            leanh::lean_dec(v___x_1433_);
                            v___x_1436_ = leanh::lean_box(0);
                            v_isShared_1437_ = v_isSharedCheck_1500_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_1425_);
                        v_a_1501_ = leanh::lean_ctor_get(v___x_1433_, 0);
                        v_isSharedCheck_1508_ =
                            (!leanh::lean_is_exclusive(v___x_1433_)) as u8;
                        if v_isSharedCheck_1508_ == 0 {
                            v___x_1503_ = v___x_1433_;
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1501_);
                            leanh::lean_dec(v___x_1433_);
                            v___x_1503_ = leanh::lean_box(0);
                            v_isShared_1504_ = v_isSharedCheck_1508_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1425_);
                    v_a_1509_ = leanh::lean_ctor_get(v___x_1432_, 0);
                    v_isSharedCheck_1516_ = (!leanh::lean_is_exclusive(v___x_1432_)) as u8;
                    if v_isSharedCheck_1516_ == 0 {
                        v___x_1511_ = v___x_1432_;
                        v_isShared_1512_ = v_isSharedCheck_1516_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1509_);
                        leanh::lean_dec(v___x_1432_);
                        v___x_1511_ = leanh::lean_box(0);
                        v_isShared_1512_ = v_isSharedCheck_1516_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1438_ = l_Lean_MVarId_congr_x3f___lam__0___closed__1;
                v___x_1439_ = leanh::lean_unsigned_to_nat(3);
                v___x_1440_ = l_Lean_Expr_isAppOfArity(v_a_1434_, v___x_1438_, v___x_1439_);
                if v___x_1440_ == 0 {
                    leanh::lean_dec(v_a_1434_);
                    leanh::lean_dec(v_mvarId_1425_);
                    v___x_1441_ = leanh::lean_box(0);
                    if v_isShared_1437_ == 0 {
                        leanh::lean_ctor_set(v___x_1436_, 0, v___x_1441_);
                        v___x_1443_ = v___x_1436_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1444_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
                        v___x_1443_ = v_reuseFailAlloc_1444_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1445_ = l_Lean_Expr_appFn_x21(v_a_1434_);
                    leanh::lean_dec(v_a_1434_);
                    v___x_1446_ = l_Lean_Expr_appArg_x21(v___x_1445_);
                    leanh::lean_dec_ref(v___x_1445_);
                    v___x_1447_ = l_Lean_Expr_cleanupAnnotations(v___x_1446_);
                    v___x_1448_ = l_Lean_Expr_isApp(v___x_1447_);
                    if v___x_1448_ == 0 {
                        leanh::lean_dec_ref(v___x_1447_);
                        leanh::lean_dec(v_mvarId_1425_);
                        v___x_1449_ = leanh::lean_box(0);
                        if v_isShared_1437_ == 0 {
                            leanh::lean_ctor_set(v___x_1436_, 0, v___x_1449_);
                            v___x_1451_ = v___x_1436_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1452_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
                            v___x_1451_ = v_reuseFailAlloc_1452_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1436_);
                        v___x_1453_ = l_Lean_Expr_getAppFn(v___x_1447_);
                        v___x_1454_ = 0;
                        v___x_1455_ = l_Lean_Expr_getAppNumArgs(v___x_1447_);
                        leanh::lean_dec_ref(v___x_1447_);
                        v___x_1456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1456_, 0, v___x_1455_);
                        v___x_1457_ = l_Lean_Meta_mkCongrSimp_x3f(
                            v___x_1453_,
                            v___x_1454_,
                            v___x_1456_,
                            v___y_1427_,
                            v___y_1428_,
                            v___y_1429_,
                            v___y_1430_,
                        );
                        if leanh::lean_obj_tag(v___x_1457_) == 0 {
                            v_a_1458_ = leanh::lean_ctor_get(v___x_1457_, 0);
                            v_isSharedCheck_1491_ =
                                (!leanh::lean_is_exclusive(v___x_1457_)) as u8;
                            if v_isSharedCheck_1491_ == 0 {
                                v___x_1460_ = v___x_1457_;
                                v_isShared_1461_ = v_isSharedCheck_1491_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1458_);
                                leanh::lean_dec(v___x_1457_);
                                v___x_1460_ = leanh::lean_box(0);
                                v_isShared_1461_ = v_isSharedCheck_1491_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_mvarId_1425_);
                            v_a_1492_ = leanh::lean_ctor_get(v___x_1457_, 0);
                            v_isSharedCheck_1499_ =
                                (!leanh::lean_is_exclusive(v___x_1457_)) as u8;
                            if v_isSharedCheck_1499_ == 0 {
                                v___x_1494_ = v___x_1457_;
                                v_isShared_1495_ = v_isSharedCheck_1499_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1492_);
                                leanh::lean_dec(v___x_1457_);
                                v___x_1494_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_1458_) == 1 {
                    leanh::lean_del_object(v___x_1460_);
                    v_val_1462_ = leanh::lean_ctor_get(v_a_1458_, 0);
                    v_isSharedCheck_1486_ = (!leanh::lean_is_exclusive(v_a_1458_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1464_ = v_a_1458_;
                        v_isShared_1465_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1462_);
                        leanh::lean_dec(v_a_1458_);
                        v___x_1464_ = leanh::lean_box(0);
                        v_isShared_1465_ = v_isSharedCheck_1486_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1458_);
                    leanh::lean_dec(v_mvarId_1425_);
                    v___x_1487_ = leanh::lean_box(0);
                    if v_isShared_1461_ == 0 {
                        leanh::lean_ctor_set(v___x_1460_, 0, v___x_1487_);
                        v___x_1489_ = v___x_1460_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
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
                if leanh::lean_obj_tag(v___x_1466_) == 0 {
                    v_a_1467_ = leanh::lean_ctor_get(v___x_1466_, 0);
                    v_isSharedCheck_1477_ = (!leanh::lean_is_exclusive(v___x_1466_)) as u8;
                    if v_isSharedCheck_1477_ == 0 {
                        v___x_1469_ = v___x_1466_;
                        v_isShared_1470_ = v_isSharedCheck_1477_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1467_);
                        leanh::lean_dec(v___x_1466_);
                        v___x_1469_ = leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1477_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1464_);
                    v_a_1478_ = leanh::lean_ctor_get(v___x_1466_, 0);
                    v_isSharedCheck_1485_ = (!leanh::lean_is_exclusive(v___x_1466_)) as u8;
                    if v_isSharedCheck_1485_ == 0 {
                        v___x_1480_ = v___x_1466_;
                        v_isShared_1481_ = v_isSharedCheck_1485_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1478_);
                        leanh::lean_dec(v___x_1466_);
                        v___x_1480_ = leanh::lean_box(0);
                        v_isShared_1481_ = v_isSharedCheck_1485_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1465_ == 0 {
                    leanh::lean_ctor_set(v___x_1464_, 0, v_a_1467_);
                    v___x_1472_ = v___x_1464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1467_);
                    v___x_1472_ = v_reuseFailAlloc_1476_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1470_ == 0 {
                    leanh::lean_ctor_set(v___x_1469_, 0, v___x_1472_);
                    v___x_1474_ = v___x_1469_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
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
                    v_reuseFailAlloc_1484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
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
                    v_reuseFailAlloc_1498_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
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
                    v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
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
                    v_reuseFailAlloc_1515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
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
    mut v_mvarId_1517_: *mut leanh::LeanObject,
    mut v___x_1518_: *mut leanh::LeanObject,
    mut v___y_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Lean_MVarId_congr_x3f___lam__0(
        v_mvarId_1517_,
        v___x_1518_,
        v___y_1519_,
        v___y_1520_,
        v___y_1521_,
        v___y_1522_,
    );
    leanh::lean_dec(v___y_1522_);
    leanh::lean_dec_ref(v___y_1521_);
    leanh::lean_dec(v___y_1520_);
    leanh::lean_dec_ref(v___y_1519_);
    return v_res_1524_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(
    mut v_x_x3f_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___y_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1538_: u8 = 0;
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_unused_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_a_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1531_ = l_Lean_Meta_saveState___redArg(v___y_1527_, v___y_1529_);
                if leanh::lean_obj_tag(v___x_1531_) == 0 {
                    v_a_1532_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    v_isSharedCheck_1576_ = (!leanh::lean_is_exclusive(v___x_1531_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1534_ = v___x_1531_;
                        v_isShared_1535_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1532_);
                        leanh::lean_dec(v___x_1531_);
                        v___x_1534_ = leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1576_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_x3f_1525_);
                    v_a_1577_ = leanh::lean_ctor_get(v___x_1531_, 0);
                    v_isSharedCheck_1584_ = (!leanh::lean_is_exclusive(v___x_1531_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v___x_1579_ = v___x_1531_;
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1577_);
                        leanh::lean_dec(v___x_1531_);
                        v___x_1579_ = leanh::lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1584_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_1529_);
                leanh::lean_inc_ref(v___y_1528_);
                leanh::lean_inc(v___y_1527_);
                leanh::lean_inc_ref(v___y_1526_);
                v___x_1563_ = leanh::lean_apply_5(
                    v_x_x3f_1525_,
                    v___y_1526_,
                    v___y_1527_,
                    v___y_1528_,
                    v___y_1529_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1563_) == 0 {
                    v_a_1564_ = leanh::lean_ctor_get(v___x_1563_, 0);
                    leanh::lean_inc(v_a_1564_);
                    if leanh::lean_obj_tag(v_a_1564_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1563_, 1);
                        v___x_1565_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_1532_,
                            v___y_1527_,
                            v___y_1529_,
                        );
                        if leanh::lean_obj_tag(v___x_1565_) == 0 {
                            leanh::lean_del_object(v___x_1534_);
                            leanh::lean_dec(v_a_1532_);
                            v_isSharedCheck_1572_ =
                                (!leanh::lean_is_exclusive(v___x_1565_)) as u8;
                            if v_isSharedCheck_1572_ == 0 {
                                v_unused_1573_ = leanh::lean_ctor_get(v___x_1565_, 0);
                                leanh::lean_dec(v_unused_1573_);
                                v___x_1567_ = v___x_1565_;
                                v_isShared_1568_ = v_isSharedCheck_1572_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1565_);
                                v___x_1567_ = leanh::lean_box(0);
                                v_isShared_1568_ = v_isSharedCheck_1572_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v_a_1574_ = leanh::lean_ctor_get(v___x_1565_, 0);
                            leanh::lean_inc(v_a_1574_);
                            leanh::lean_dec_ref_known(v___x_1565_, 1);
                            v_a_1560_ = v_a_1574_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_1564_, 1);
                        leanh::lean_del_object(v___x_1534_);
                        leanh::lean_dec(v_a_1532_);
                        return v___x_1563_;
                    }
                } else {
                    v_a_1575_ = leanh::lean_ctor_get(v___x_1563_, 0);
                    leanh::lean_inc(v_a_1575_);
                    leanh::lean_dec_ref_known(v___x_1563_, 1);
                    v_a_1560_ = v_a_1575_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                if v___y_1538_ == 0 {
                    leanh::lean_del_object(v___x_1534_);
                    v___x_1539_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1532_,
                        v___y_1527_,
                        v___y_1529_,
                    );
                    leanh::lean_dec(v_a_1532_);
                    if leanh::lean_obj_tag(v___x_1539_) == 0 {
                        v_isSharedCheck_1546_ =
                            (!leanh::lean_is_exclusive(v___x_1539_)) as u8;
                        if v_isSharedCheck_1546_ == 0 {
                            v_unused_1547_ = leanh::lean_ctor_get(v___x_1539_, 0);
                            leanh::lean_dec(v_unused_1547_);
                            v___x_1541_ = v___x_1539_;
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1539_);
                            v___x_1541_ = leanh::lean_box(0);
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_1537_);
                        v_a_1548_ = leanh::lean_ctor_get(v___x_1539_, 0);
                        v_isSharedCheck_1555_ =
                            (!leanh::lean_is_exclusive(v___x_1539_)) as u8;
                        if v_isSharedCheck_1555_ == 0 {
                            v___x_1550_ = v___x_1539_;
                            v_isShared_1551_ = v_isSharedCheck_1555_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1548_);
                            leanh::lean_dec(v___x_1539_);
                            v___x_1550_ = leanh::lean_box(0);
                            v_isShared_1551_ = v_isSharedCheck_1555_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1532_);
                    if v_isShared_1535_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1534_, 1);
                        leanh::lean_ctor_set(v___x_1534_, 0, v___y_1537_);
                        v___x_1557_ = v___x_1534_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___y_1537_);
                        v___x_1557_ = v_reuseFailAlloc_1558_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1542_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1541_, 1);
                    leanh::lean_ctor_set(v___x_1541_, 0, v___y_1537_);
                    v___x_1544_ = v___x_1541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___y_1537_);
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
                    v_reuseFailAlloc_1554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
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
                    leanh::lean_inc_ref(v_a_1560_);
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
                    leanh::lean_ctor_set(v___x_1567_, 0, v_a_1564_);
                    v___x_1570_ = v___x_1567_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1564_);
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
                    v_reuseFailAlloc_1583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
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
    mut v_x_x3f_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
    leanh::lean_dec(v___y_1589_);
    leanh::lean_dec_ref(v___y_1588_);
    leanh::lean_dec(v___y_1587_);
    leanh::lean_dec_ref(v___y_1586_);
    return v_res_1591_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
    mut v_x_x3f_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: u8 = 0;
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1604_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut v_unused_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1598_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
                if leanh::lean_obj_tag(v___x_1598_) == 0 {
                    return v___x_1598_;
                } else {
                    v_a_1599_ = leanh::lean_ctor_get(v___x_1598_, 0);
                    leanh::lean_inc(v_a_1599_);
                    v___x_1611_ = l_Lean_Exception_isInterrupt(v_a_1599_);
                    if v___x_1611_ == 0 {
                        v___x_1612_ = l_Lean_Exception_isRuntime(v_a_1599_);
                        v___y_1601_ = v___x_1612_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_1599_);
                        v___y_1601_ = v___x_1611_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1601_ == 0 {
                    v_isSharedCheck_1609_ = (!leanh::lean_is_exclusive(v___x_1598_)) as u8;
                    if v_isSharedCheck_1609_ == 0 {
                        v_unused_1610_ = leanh::lean_ctor_get(v___x_1598_, 0);
                        leanh::lean_dec(v_unused_1610_);
                        v___x_1603_ = v___x_1598_;
                        v_isShared_1604_ = v_isSharedCheck_1609_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1598_);
                        v___x_1603_ = leanh::lean_box(0);
                        v_isShared_1604_ = v_isSharedCheck_1609_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_1598_;
                }
            }
            2 => {
                v___x_1605_ = leanh::lean_box(0);
                if v_isShared_1604_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1603_, 0);
                    leanh::lean_ctor_set(v___x_1603_, 0, v___x_1605_);
                    v___x_1607_ = v___x_1603_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
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
    mut v_x_x3f_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___redArg(
        v_x_x3f_1613_,
        v___y_1614_,
        v___y_1615_,
        v___y_1616_,
        v___y_1617_,
    );
    leanh::lean_dec(v___y_1617_);
    leanh::lean_dec_ref(v___y_1616_);
    leanh::lean_dec(v___y_1615_);
    leanh::lean_dec_ref(v___y_1614_);
    return v_res_1619_;
}
pub unsafe fn l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(
    mut v_00_u03b1_1620_: *mut leanh::LeanObject,
    mut v_x_x3f_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1628_: *mut leanh::LeanObject,
    mut v_x_x3f_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
    mut v___y_1632_: *mut leanh::LeanObject,
    mut v___y_1633_: *mut leanh::LeanObject,
    mut v___y_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0(
        v_00_u03b1_1628_,
        v_x_x3f_1629_,
        v___y_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
    );
    leanh::lean_dec(v___y_1633_);
    leanh::lean_dec_ref(v___y_1632_);
    leanh::lean_dec(v___y_1631_);
    leanh::lean_dec_ref(v___y_1630_);
    return v_res_1635_;
}
pub unsafe fn l_Lean_MVarId_congr_x3f(
    mut v_mvarId_1639_: *mut leanh::LeanObject,
    mut v_a_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
    mut v_a_1642_: *mut leanh::LeanObject,
    mut v_a_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_MVarId_congr_x3f___closed__1;
    leanh::lean_inc(v_mvarId_1639_);
    v___f_1646_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_congr_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1646_, 0, v_mvarId_1639_);
    leanh::lean_closure_set(v___f_1646_, 1, v___x_1645_);
    v___x_1647_ = leanh::lean_alloc_closure(
        l_Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_1647_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1647_, 1, v___f_1646_);
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
    mut v_mvarId_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ =
        l_Lean_MVarId_congr_x3f(v_mvarId_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
    leanh::lean_dec(v_a_1653_);
    leanh::lean_dec_ref(v_a_1652_);
    leanh::lean_dec(v_a_1651_);
    leanh::lean_dec_ref(v_a_1650_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(
    mut v_00_u03b1_1656_: *mut leanh::LeanObject,
    mut v_x_x3f_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(v_x_x3f_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1664_: *mut leanh::LeanObject,
    mut v_x_x3f_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_commitWhenSome_x3f___at___00Lean_commitWhenSomeNoEx_x3f___at___00Lean_MVarId_congr_x3f_spec__0_spec__0(v_00_u03b1_1664_, v_x_x3f_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
    leanh::lean_dec(v___y_1669_);
    leanh::lean_dec_ref(v___y_1668_);
    leanh::lean_dec(v___y_1667_);
    leanh::lean_dec_ref(v___y_1666_);
    return v_res_1671_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__0(
    mut v_a_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1685_: u8 = 0;
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1710_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_1675_);
                v___x_1681_ = l_Lean_MVarId_getType_x27(
                    v_a_1675_,
                    v___y_1676_,
                    v___y_1677_,
                    v___y_1678_,
                    v___y_1679_,
                );
                if leanh::lean_obj_tag(v___x_1681_) == 0 {
                    v_a_1682_ = leanh::lean_ctor_get(v___x_1681_, 0);
                    v_isSharedCheck_1732_ = (!leanh::lean_is_exclusive(v___x_1681_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1684_ = v___x_1681_;
                        v_isShared_1685_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1682_);
                        leanh::lean_dec(v___x_1681_);
                        v___x_1684_ = leanh::lean_box(0);
                        v_isShared_1685_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1675_);
                    v_a_1733_ = leanh::lean_ctor_get(v___x_1681_, 0);
                    v_isSharedCheck_1740_ = (!leanh::lean_is_exclusive(v___x_1681_)) as u8;
                    if v_isSharedCheck_1740_ == 0 {
                        v___x_1735_ = v___x_1681_;
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1733_);
                        leanh::lean_dec(v___x_1681_);
                        v___x_1735_ = leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1686_ = l_Lean_MVarId_hcongr_x3f___lam__0___closed__1;
                v___x_1687_ = leanh::lean_unsigned_to_nat(4);
                v___x_1688_ = l_Lean_Expr_isAppOfArity(v_a_1682_, v___x_1686_, v___x_1687_);
                if v___x_1688_ == 0 {
                    leanh::lean_dec(v_a_1682_);
                    leanh::lean_dec(v_a_1675_);
                    v___x_1689_ = leanh::lean_box(0);
                    if v_isShared_1685_ == 0 {
                        leanh::lean_ctor_set(v___x_1684_, 0, v___x_1689_);
                        v___x_1691_ = v___x_1684_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
                        v___x_1691_ = v_reuseFailAlloc_1692_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1693_ = l_Lean_Expr_appFn_x21(v_a_1682_);
                    leanh::lean_dec(v_a_1682_);
                    v___x_1694_ = l_Lean_Expr_appFn_x21(v___x_1693_);
                    leanh::lean_dec_ref(v___x_1693_);
                    v___x_1695_ = l_Lean_Expr_appArg_x21(v___x_1694_);
                    leanh::lean_dec_ref(v___x_1694_);
                    v___x_1696_ = l_Lean_Expr_cleanupAnnotations(v___x_1695_);
                    v___x_1697_ = l_Lean_Expr_isApp(v___x_1696_);
                    if v___x_1697_ == 0 {
                        leanh::lean_dec_ref(v___x_1696_);
                        leanh::lean_dec(v_a_1675_);
                        v___x_1698_ = leanh::lean_box(0);
                        if v_isShared_1685_ == 0 {
                            leanh::lean_ctor_set(v___x_1684_, 0, v___x_1698_);
                            v___x_1700_ = v___x_1684_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1701_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                            v___x_1700_ = v_reuseFailAlloc_1701_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1684_);
                        v___x_1702_ = l_Lean_Expr_getAppFn(v___x_1696_);
                        v___x_1703_ = l_Lean_Expr_getAppNumArgs(v___x_1696_);
                        leanh::lean_dec_ref(v___x_1696_);
                        v___x_1704_ = l_Lean_Meta_mkHCongrWithArity(
                            v___x_1702_,
                            v___x_1703_,
                            v___y_1676_,
                            v___y_1677_,
                            v___y_1678_,
                            v___y_1679_,
                        );
                        if leanh::lean_obj_tag(v___x_1704_) == 0 {
                            v_a_1705_ = leanh::lean_ctor_get(v___x_1704_, 0);
                            leanh::lean_inc(v_a_1705_);
                            leanh::lean_dec_ref_known(v___x_1704_, 1);
                            v___x_1706_ =
                                l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(
                                    v_a_1675_,
                                    v_a_1705_,
                                    v___y_1676_,
                                    v___y_1677_,
                                    v___y_1678_,
                                    v___y_1679_,
                                );
                            if leanh::lean_obj_tag(v___x_1706_) == 0 {
                                v_a_1707_ = leanh::lean_ctor_get(v___x_1706_, 0);
                                v_isSharedCheck_1715_ =
                                    (!leanh::lean_is_exclusive(v___x_1706_)) as u8;
                                if v_isSharedCheck_1715_ == 0 {
                                    v___x_1709_ = v___x_1706_;
                                    v_isShared_1710_ = v_isSharedCheck_1715_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1707_);
                                    leanh::lean_dec(v___x_1706_);
                                    v___x_1709_ = leanh::lean_box(0);
                                    v_isShared_1710_ = v_isSharedCheck_1715_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_1716_ = leanh::lean_ctor_get(v___x_1706_, 0);
                                v_isSharedCheck_1723_ =
                                    (!leanh::lean_is_exclusive(v___x_1706_)) as u8;
                                if v_isSharedCheck_1723_ == 0 {
                                    v___x_1718_ = v___x_1706_;
                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1716_);
                                    leanh::lean_dec(v___x_1706_);
                                    v___x_1718_ = leanh::lean_box(0);
                                    v_isShared_1719_ = v_isSharedCheck_1723_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1675_);
                            v_a_1724_ = leanh::lean_ctor_get(v___x_1704_, 0);
                            v_isSharedCheck_1731_ =
                                (!leanh::lean_is_exclusive(v___x_1704_)) as u8;
                            if v_isSharedCheck_1731_ == 0 {
                                v___x_1726_ = v___x_1704_;
                                v_isShared_1727_ = v_isSharedCheck_1731_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1724_);
                                leanh::lean_dec(v___x_1704_);
                                v___x_1726_ = leanh::lean_box(0);
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
                v___x_1711_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1711_, 0, v_a_1707_);
                if v_isShared_1710_ == 0 {
                    leanh::lean_ctor_set(v___x_1709_, 0, v___x_1711_);
                    v___x_1713_ = v___x_1709_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
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
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
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
                    v_reuseFailAlloc_1730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
                    v_reuseFailAlloc_1739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
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
    mut v_a_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_Lean_MVarId_hcongr_x3f___lam__0(
        v_a_1741_,
        v___y_1742_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
    );
    leanh::lean_dec(v___y_1745_);
    leanh::lean_dec_ref(v___y_1744_);
    leanh::lean_dec(v___y_1743_);
    leanh::lean_dec_ref(v___y_1742_);
    return v_res_1747_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f___lam__1(
    mut v_mvarId_1748_: *mut leanh::LeanObject,
    mut v___x_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_a_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1771_: u8 = 0;
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1748_);
                v___x_1755_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1748_,
                    v___x_1749_,
                    v___y_1750_,
                    v___y_1751_,
                    v___y_1752_,
                    v___y_1753_,
                );
                if leanh::lean_obj_tag(v___x_1755_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1755_, 1);
                    v___x_1756_ = l_Lean_MVarId_eqOfHEq(
                        v_mvarId_1748_,
                        v___y_1750_,
                        v___y_1751_,
                        v___y_1752_,
                        v___y_1753_,
                    );
                    if leanh::lean_obj_tag(v___x_1756_) == 0 {
                        v_a_1757_ = leanh::lean_ctor_get(v___x_1756_, 0);
                        leanh::lean_inc_n(v_a_1757_, 2);
                        leanh::lean_dec_ref_known(v___x_1756_, 1);
                        v___f_1758_ = leanh::lean_alloc_closure(
                            l_Lean_MVarId_hcongr_x3f___lam__0___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        leanh::lean_closure_set(v___f_1758_, 0, v_a_1757_);
                        v___x_1759_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_congr_x3f_spec__1___redArg(v_a_1757_, v___f_1758_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
                        return v___x_1759_;
                    } else {
                        v_a_1760_ = leanh::lean_ctor_get(v___x_1756_, 0);
                        v_isSharedCheck_1767_ =
                            (!leanh::lean_is_exclusive(v___x_1756_)) as u8;
                        if v_isSharedCheck_1767_ == 0 {
                            v___x_1762_ = v___x_1756_;
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1760_);
                            leanh::lean_dec(v___x_1756_);
                            v___x_1762_ = leanh::lean_box(0);
                            v_isShared_1763_ = v_isSharedCheck_1767_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1748_);
                    v_a_1768_ = leanh::lean_ctor_get(v___x_1755_, 0);
                    v_isSharedCheck_1775_ = (!leanh::lean_is_exclusive(v___x_1755_)) as u8;
                    if v_isSharedCheck_1775_ == 0 {
                        v___x_1770_ = v___x_1755_;
                        v_isShared_1771_ = v_isSharedCheck_1775_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1768_);
                        leanh::lean_dec(v___x_1755_);
                        v___x_1770_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
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
                    v_reuseFailAlloc_1774_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
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
    mut v_mvarId_1776_: *mut leanh::LeanObject,
    mut v___x_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: *mut leanh::LeanObject,
    mut v___y_1779_: *mut leanh::LeanObject,
    mut v___y_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1783_ = l_Lean_MVarId_hcongr_x3f___lam__1(
        v_mvarId_1776_,
        v___x_1777_,
        v___y_1778_,
        v___y_1779_,
        v___y_1780_,
        v___y_1781_,
    );
    leanh::lean_dec(v___y_1781_);
    leanh::lean_dec_ref(v___y_1780_);
    leanh::lean_dec(v___y_1779_);
    leanh::lean_dec_ref(v___y_1778_);
    return v_res_1783_;
}
pub unsafe fn l_Lean_MVarId_hcongr_x3f(
    mut v_mvarId_1784_: *mut leanh::LeanObject,
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Lean_MVarId_congr_x3f___closed__1;
    v___f_1791_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_hcongr_x3f___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1791_, 0, v_mvarId_1784_);
    leanh::lean_closure_set(v___f_1791_, 1, v___x_1790_);
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
    mut v_mvarId_1793_: *mut leanh::LeanObject,
    mut v_a_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ =
        l_Lean_MVarId_hcongr_x3f(v_mvarId_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
    leanh::lean_dec(v_a_1797_);
    leanh::lean_dec_ref(v_a_1796_);
    leanh::lean_dec(v_a_1795_);
    leanh::lean_dec_ref(v_a_1794_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
    mut v_x_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1812_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1817_: u8 = 0;
    let mut v_a_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___y_1823_: u8 = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut v_unused_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1837_: u8 = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut v_a_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1851_: u8 = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1806_ = l_Lean_Meta_saveState___redArg(v___y_1802_, v___y_1804_);
                if leanh::lean_obj_tag(v___x_1806_) == 0 {
                    v_a_1807_ = leanh::lean_ctor_get(v___x_1806_, 0);
                    leanh::lean_inc(v_a_1807_);
                    leanh::lean_dec_ref_known(v___x_1806_, 1);
                    leanh::lean_inc(v___y_1804_);
                    leanh::lean_inc_ref(v___y_1803_);
                    leanh::lean_inc(v___y_1802_);
                    leanh::lean_inc_ref(v___y_1801_);
                    v___x_1808_ = leanh::lean_apply_5(
                        v_x_1800_,
                        v___y_1801_,
                        v___y_1802_,
                        v___y_1803_,
                        v___y_1804_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1808_) == 0 {
                        leanh::lean_dec(v_a_1807_);
                        v_a_1809_ = leanh::lean_ctor_get(v___x_1808_, 0);
                        v_isSharedCheck_1817_ =
                            (!leanh::lean_is_exclusive(v___x_1808_)) as u8;
                        if v_isSharedCheck_1817_ == 0 {
                            v___x_1811_ = v___x_1808_;
                            v_isShared_1812_ = v_isSharedCheck_1817_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1809_);
                            leanh::lean_dec(v___x_1808_);
                            v___x_1811_ = leanh::lean_box(0);
                            v_isShared_1812_ = v_isSharedCheck_1817_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1818_ = leanh::lean_ctor_get(v___x_1808_, 0);
                        v_isSharedCheck_1847_ =
                            (!leanh::lean_is_exclusive(v___x_1808_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v___x_1820_ = v___x_1808_;
                            v_isShared_1821_ = v_isSharedCheck_1847_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1818_);
                            leanh::lean_dec(v___x_1808_);
                            v___x_1820_ = leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_1847_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1800_);
                    v_a_1848_ = leanh::lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1855_ = (!leanh::lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1850_ = v___x_1806_;
                        v_isShared_1851_ = v_isSharedCheck_1855_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1848_);
                        leanh::lean_dec(v___x_1806_);
                        v___x_1850_ = leanh::lean_box(0);
                        v_isShared_1851_ = v_isSharedCheck_1855_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1813_, 0, v_a_1809_);
                if v_isShared_1812_ == 0 {
                    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1813_);
                    v___x_1815_ = v___x_1811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1816_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
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
                    leanh::lean_inc(v_a_1818_);
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
                    leanh::lean_del_object(v___x_1820_);
                    leanh::lean_dec(v_a_1818_);
                    v___x_1824_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_1807_,
                        v___y_1802_,
                        v___y_1804_,
                    );
                    leanh::lean_dec(v_a_1807_);
                    if leanh::lean_obj_tag(v___x_1824_) == 0 {
                        v_isSharedCheck_1832_ =
                            (!leanh::lean_is_exclusive(v___x_1824_)) as u8;
                        if v_isSharedCheck_1832_ == 0 {
                            v_unused_1833_ = leanh::lean_ctor_get(v___x_1824_, 0);
                            leanh::lean_dec(v_unused_1833_);
                            v___x_1826_ = v___x_1824_;
                            v_isShared_1827_ = v_isSharedCheck_1832_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1824_);
                            v___x_1826_ = leanh::lean_box(0);
                            v_isShared_1827_ = v_isSharedCheck_1832_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1834_ = leanh::lean_ctor_get(v___x_1824_, 0);
                        v_isSharedCheck_1841_ =
                            (!leanh::lean_is_exclusive(v___x_1824_)) as u8;
                        if v_isSharedCheck_1841_ == 0 {
                            v___x_1836_ = v___x_1824_;
                            v_isShared_1837_ = v_isSharedCheck_1841_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1834_);
                            leanh::lean_dec(v___x_1824_);
                            v___x_1836_ = leanh::lean_box(0);
                            v_isShared_1837_ = v_isSharedCheck_1841_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1807_);
                    if v_isShared_1821_ == 0 {
                        v___x_1843_ = v___x_1820_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1818_);
                        v___x_1843_ = v_reuseFailAlloc_1844_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1828_ = leanh::lean_box(0);
                if v_isShared_1827_ == 0 {
                    leanh::lean_ctor_set(v___x_1826_, 0, v___x_1828_);
                    v___x_1830_ = v___x_1826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
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
                    v_reuseFailAlloc_1840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
                    v_reuseFailAlloc_1854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
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
    mut v_x_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
    mut v___y_1861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1862_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
        v_x_1856_,
        v___y_1857_,
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
    );
    leanh::lean_dec(v___y_1860_);
    leanh::lean_dec_ref(v___y_1859_);
    leanh::lean_dec(v___y_1858_);
    leanh::lean_dec_ref(v___y_1857_);
    return v_res_1862_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(
    mut v_00_u03b1_1863_: *mut leanh::LeanObject,
    mut v_x_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1871_: *mut leanh::LeanObject,
    mut v_x_1872_: *mut leanh::LeanObject,
    mut v___y_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1878_ = l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1(
        v_00_u03b1_1871_,
        v_x_1872_,
        v___y_1873_,
        v___y_1874_,
        v___y_1875_,
        v___y_1876_,
    );
    leanh::lean_dec(v___y_1876_);
    leanh::lean_dec_ref(v___y_1875_);
    leanh::lean_dec(v___y_1874_);
    leanh::lean_dec_ref(v___y_1873_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(
    mut v_msgData_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
    mut v___y_1883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = lean_st_ref_get(v___y_1883_);
    v_env_1886_ = leanh::lean_ctor_get(v___x_1885_, 0);
    leanh::lean_inc_ref(v_env_1886_);
    leanh::lean_dec(v___x_1885_);
    v___x_1887_ = lean_st_ref_get(v___y_1881_);
    v_mctx_1888_ = leanh::lean_ctor_get(v___x_1887_, 0);
    leanh::lean_inc_ref(v_mctx_1888_);
    leanh::lean_dec(v___x_1887_);
    v_lctx_1889_ = leanh::lean_ctor_get(v___y_1880_, 2);
    v_options_1890_ = leanh::lean_ctor_get(v___y_1882_, 2);
    leanh::lean_inc_ref(v_options_1890_);
    leanh::lean_inc_ref(v_lctx_1889_);
    v___x_1891_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1891_, 0, v_env_1886_);
    leanh::lean_ctor_set(v___x_1891_, 1, v_mctx_1888_);
    leanh::lean_ctor_set(v___x_1891_, 2, v_lctx_1889_);
    leanh::lean_ctor_set(v___x_1891_, 3, v_options_1890_);
    v___x_1892_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    leanh::lean_ctor_set(v___x_1892_, 1, v_msgData_1879_);
    v___x_1893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
    return v___x_1893_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(
    mut v_msgData_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
    mut v___y_1896_: *mut leanh::LeanObject,
    mut v___y_1897_: *mut leanh::LeanObject,
    mut v___y_1898_: *mut leanh::LeanObject,
    mut v___y_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1900_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msgData_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
    leanh::lean_dec(v___y_1898_);
    leanh::lean_dec_ref(v___y_1897_);
    leanh::lean_dec(v___y_1896_);
    leanh::lean_dec_ref(v___y_1895_);
    return v_res_1900_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
    mut v_msg_1901_: *mut leanh::LeanObject,
    mut v___y_1902_: *mut leanh::LeanObject,
    mut v___y_1903_: *mut leanh::LeanObject,
    mut v___y_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1912_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1907_ = leanh::lean_ctor_get(v___y_1904_, 5);
                v___x_1908_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0_spec__0(v_msg_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
                v_a_1909_ = leanh::lean_ctor_get(v___x_1908_, 0);
                v_isSharedCheck_1917_ = (!leanh::lean_is_exclusive(v___x_1908_)) as u8;
                if v_isSharedCheck_1917_ == 0 {
                    v___x_1911_ = v___x_1908_;
                    v_isShared_1912_ = v_isSharedCheck_1917_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1909_);
                    leanh::lean_dec(v___x_1908_);
                    v___x_1911_ = leanh::lean_box(0);
                    v_isShared_1912_ = v_isSharedCheck_1917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1907_);
                v___x_1913_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1913_, 0, v_ref_1907_);
                leanh::lean_ctor_set(v___x_1913_, 1, v_a_1909_);
                if v_isShared_1912_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1911_, 1);
                    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1913_);
                    v___x_1915_ = v___x_1911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
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
    mut v_msg_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0___redArg(
        v_msg_1918_,
        v___y_1919_,
        v___y_1920_,
        v___y_1921_,
        v___y_1922_,
    );
    leanh::lean_dec(v___y_1922_);
    leanh::lean_dec_ref(v___y_1921_);
    leanh::lean_dec(v___y_1920_);
    leanh::lean_dec_ref(v___y_1919_);
    return v_res_1924_;
}
pub unsafe fn _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1;
    v___x_1931_ = l_Lean_stringToMessageData(v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1933_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3;
    v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f___lam__0(
    mut v___x_1935_: *mut leanh::LeanObject,
    mut v_mvarId_1936_: *mut leanh::LeanObject,
    mut v___y_1937_: *mut leanh::LeanObject,
    mut v___y_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
    mut v___y_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___y_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1967_: u8 = 0;
    let mut v_head_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_unused_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_a_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1990_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_1935_);
                v___x_1942_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v___x_1935_,
                    v___y_1937_,
                    v___y_1938_,
                    v___y_1939_,
                    v___y_1940_,
                );
                if leanh::lean_obj_tag(v___x_1942_) == 0 {
                    v_a_1943_ = leanh::lean_ctor_get(v___x_1942_, 0);
                    leanh::lean_inc(v_a_1943_);
                    leanh::lean_dec_ref_known(v___x_1942_, 1);
                    v___x_1944_ = 0;
                    v___x_1945_ = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0;
                    v___x_1946_ = leanh::lean_box(0);
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
                    if leanh::lean_obj_tag(v___x_1947_) == 0 {
                        v_a_1948_ = leanh::lean_ctor_get(v___x_1947_, 0);
                        v_isSharedCheck_1986_ =
                            (!leanh::lean_is_exclusive(v___x_1947_)) as u8;
                        if v_isSharedCheck_1986_ == 0 {
                            v___x_1950_ = v___x_1947_;
                            v_isShared_1951_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1948_);
                            leanh::lean_dec(v___x_1947_);
                            v___x_1950_ = leanh::lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_1986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1935_);
                        return v___x_1947_;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_1936_);
                    leanh::lean_dec(v___x_1935_);
                    v_a_1987_ = leanh::lean_ctor_get(v___x_1942_, 0);
                    v_isSharedCheck_1994_ = (!leanh::lean_is_exclusive(v___x_1942_)) as u8;
                    if v_isSharedCheck_1994_ == 0 {
                        v___x_1989_ = v___x_1942_;
                        v_isShared_1990_ = v_isSharedCheck_1994_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1987_);
                        leanh::lean_dec(v___x_1942_);
                        v___x_1989_ = leanh::lean_box(0);
                        v_isShared_1990_ = v_isSharedCheck_1994_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1948_) == 1 {
                    v_tail_1963_ = leanh::lean_ctor_get(v_a_1948_, 1);
                    leanh::lean_inc(v_tail_1963_);
                    if leanh::lean_obj_tag(v_tail_1963_) == 1 {
                        leanh::lean_dec(v___x_1935_);
                        v_head_1964_ = leanh::lean_ctor_get(v_a_1948_, 0);
                        v_isSharedCheck_1984_ = (!leanh::lean_is_exclusive(v_a_1948_)) as u8;
                        if v_isSharedCheck_1984_ == 0 {
                            v_unused_1985_ = leanh::lean_ctor_get(v_a_1948_, 1);
                            leanh::lean_dec(v_unused_1985_);
                            v___x_1966_ = v_a_1948_;
                            v_isShared_1967_ = v_isSharedCheck_1984_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_1964_);
                            leanh::lean_dec(v_a_1948_);
                            v___x_1966_ = leanh::lean_box(0);
                            v_isShared_1967_ = v_isSharedCheck_1984_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_1963_);
                        leanh::lean_dec_ref_known(v_a_1948_, 2);
                        leanh::lean_del_object(v___x_1950_);
                        v___y_1953_ = v___y_1937_;
                        v___y_1954_ = v___y_1938_;
                        v___y_1955_ = v___y_1939_;
                        v___y_1956_ = v___y_1940_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1950_);
                    leanh::lean_dec(v_a_1948_);
                    v___y_1953_ = v___y_1937_;
                    v___y_1954_ = v___y_1938_;
                    v___y_1955_ = v___y_1939_;
                    v___y_1956_ = v___y_1940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1957_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2_once
                    ),
                    _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2,
                );
                v___x_1958_ = l_Lean_MessageData_ofConstName(v___x_1935_, v___x_1944_);
                v___x_1959_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1959_, 0, v___x_1957_);
                leanh::lean_ctor_set(v___x_1959_, 1, v___x_1958_);
                v___x_1960_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4_once
                    ),
                    _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4,
                );
                v___x_1961_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1961_, 0, v___x_1959_);
                leanh::lean_ctor_set(v___x_1961_, 1, v___x_1960_);
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
                v_head_1968_ = leanh::lean_ctor_get(v_tail_1963_, 0);
                v_isSharedCheck_1982_ = (!leanh::lean_is_exclusive(v_tail_1963_)) as u8;
                if v_isSharedCheck_1982_ == 0 {
                    v_unused_1983_ = leanh::lean_ctor_get(v_tail_1963_, 1);
                    leanh::lean_dec(v_unused_1983_);
                    v___x_1970_ = v_tail_1963_;
                    v_isShared_1971_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_head_1968_);
                    leanh::lean_dec(v_tail_1963_);
                    v___x_1970_ = leanh::lean_box(0);
                    v_isShared_1971_ = v_isSharedCheck_1982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1972_ = leanh::lean_box(0);
                if v_isShared_1971_ == 0 {
                    leanh::lean_ctor_set(v___x_1970_, 1, v___x_1972_);
                    v___x_1974_ = v___x_1970_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_head_1968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1972_);
                    v___x_1974_ = v_reuseFailAlloc_1981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1967_ == 0 {
                    leanh::lean_ctor_set(v___x_1966_, 1, v___x_1974_);
                    v___x_1976_ = v___x_1966_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1980_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_head_1964_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1974_);
                    v___x_1976_ = v_reuseFailAlloc_1980_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1951_ == 0 {
                    leanh::lean_ctor_set(v___x_1950_, 0, v___x_1976_);
                    v___x_1978_ = v___x_1950_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
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
                    v_reuseFailAlloc_1993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
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
    mut v___x_1995_: *mut leanh::LeanObject,
    mut v_mvarId_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l_Lean_MVarId_congrImplies_x3f___lam__0(
        v___x_1995_,
        v_mvarId_1996_,
        v___y_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
    );
    leanh::lean_dec(v___y_2000_);
    leanh::lean_dec_ref(v___y_1999_);
    leanh::lean_dec(v___y_1998_);
    leanh::lean_dec_ref(v___y_1997_);
    return v_res_2002_;
}
pub unsafe fn l_Lean_MVarId_congrImplies_x3f(
    mut v_mvarId_2006_: *mut leanh::LeanObject,
    mut v_a_2007_: *mut leanh::LeanObject,
    mut v_a_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_a_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Lean_MVarId_congrImplies_x3f___closed__1;
    v___f_2013_ = leanh::lean_alloc_closure(
        l_Lean_MVarId_congrImplies_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2013_, 0, v___x_2012_);
    leanh::lean_closure_set(v___f_2013_, 1, v_mvarId_2006_);
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
    mut v_mvarId_2015_: *mut leanh::LeanObject,
    mut v_a_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
    mut v_a_2019_: *mut leanh::LeanObject,
    mut v_a_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ =
        l_Lean_MVarId_congrImplies_x3f(v_mvarId_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
    leanh::lean_dec(v_a_2019_);
    leanh::lean_dec_ref(v_a_2018_);
    leanh::lean_dec(v_a_2017_);
    leanh::lean_dec_ref(v_a_2016_);
    return v_res_2021_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(
    mut v_00_u03b1_2022_: *mut leanh::LeanObject,
    mut v_msg_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
    mut v___y_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2030_: *mut leanh::LeanObject,
    mut v_msg_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
    mut v___y_2034_: *mut leanh::LeanObject,
    mut v___y_2035_: *mut leanh::LeanObject,
    mut v___y_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2037_ = l_Lean_throwError___at___00Lean_MVarId_congrImplies_x3f_spec__0(
        v_00_u03b1_2030_,
        v_msg_2031_,
        v___y_2032_,
        v___y_2033_,
        v___y_2034_,
        v___y_2035_,
    );
    leanh::lean_dec(v___y_2035_);
    leanh::lean_dec_ref(v___y_2034_);
    leanh::lean_dec(v___y_2033_);
    leanh::lean_dec_ref(v___y_2032_);
    return v_res_2037_;
}
pub unsafe fn _init_l_Lean_MVarId_congrCore___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = l_Lean_MVarId_congrCore___closed__1;
    v___x_2042_ = l_Lean_MessageData_ofFormat(v___x_2041_);
    return v___x_2042_;
}
pub unsafe fn _init_l_Lean_MVarId_congrCore___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_congrCore___closed__2_once),
        _init_l_Lean_MVarId_congrCore___closed__2,
    );
    v___x_2044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_MVarId_congrCore(
    mut v_mvarId_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
    mut v_a_2047_: *mut leanh::LeanObject,
    mut v_a_2048_: *mut leanh::LeanObject,
    mut v_a_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v_val_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v_val_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2073_: u8 = 0;
    let mut v_val_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut v_a_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_isSharedCheck_2090_: u8 = 0;
    let mut v_a_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut v_a_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_2045_);
                v___x_2051_ = l_Lean_MVarId_congr_x3f(
                    v_mvarId_2045_,
                    v_a_2046_,
                    v_a_2047_,
                    v_a_2048_,
                    v_a_2049_,
                );
                if leanh::lean_obj_tag(v___x_2051_) == 0 {
                    v_a_2052_ = leanh::lean_ctor_get(v___x_2051_, 0);
                    v_isSharedCheck_2099_ = (!leanh::lean_is_exclusive(v___x_2051_)) as u8;
                    if v_isSharedCheck_2099_ == 0 {
                        v___x_2054_ = v___x_2051_;
                        v_isShared_2055_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2052_);
                        leanh::lean_dec(v___x_2051_);
                        v___x_2054_ = leanh::lean_box(0);
                        v_isShared_2055_ = v_isSharedCheck_2099_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mvarId_2045_);
                    v_a_2100_ = leanh::lean_ctor_get(v___x_2051_, 0);
                    v_isSharedCheck_2107_ = (!leanh::lean_is_exclusive(v___x_2051_)) as u8;
                    if v_isSharedCheck_2107_ == 0 {
                        v___x_2102_ = v___x_2051_;
                        v_isShared_2103_ = v_isSharedCheck_2107_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2100_);
                        leanh::lean_dec(v___x_2051_);
                        v___x_2102_ = leanh::lean_box(0);
                        v_isShared_2103_ = v_isSharedCheck_2107_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2052_) == 1 {
                    leanh::lean_dec(v_mvarId_2045_);
                    v_val_2056_ = leanh::lean_ctor_get(v_a_2052_, 0);
                    leanh::lean_inc(v_val_2056_);
                    leanh::lean_dec_ref_known(v_a_2052_, 1);
                    if v_isShared_2055_ == 0 {
                        leanh::lean_ctor_set(v___x_2054_, 0, v_val_2056_);
                        v___x_2058_ = v___x_2054_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_val_2056_);
                        v___x_2058_ = v_reuseFailAlloc_2059_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2054_);
                    leanh::lean_dec(v_a_2052_);
                    leanh::lean_inc(v_mvarId_2045_);
                    v___x_2060_ = l_Lean_MVarId_hcongr_x3f(
                        v_mvarId_2045_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                    );
                    if leanh::lean_obj_tag(v___x_2060_) == 0 {
                        v_a_2061_ = leanh::lean_ctor_get(v___x_2060_, 0);
                        v_isSharedCheck_2090_ =
                            (!leanh::lean_is_exclusive(v___x_2060_)) as u8;
                        if v_isSharedCheck_2090_ == 0 {
                            v___x_2063_ = v___x_2060_;
                            v_isShared_2064_ = v_isSharedCheck_2090_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2061_);
                            leanh::lean_dec(v___x_2060_);
                            v___x_2063_ = leanh::lean_box(0);
                            v_isShared_2064_ = v_isSharedCheck_2090_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_2045_);
                        v_a_2091_ = leanh::lean_ctor_get(v___x_2060_, 0);
                        v_isSharedCheck_2098_ =
                            (!leanh::lean_is_exclusive(v___x_2060_)) as u8;
                        if v_isSharedCheck_2098_ == 0 {
                            v___x_2093_ = v___x_2060_;
                            v_isShared_2094_ = v_isSharedCheck_2098_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2091_);
                            leanh::lean_dec(v___x_2060_);
                            v___x_2093_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_2061_) == 1 {
                    leanh::lean_dec(v_mvarId_2045_);
                    v_val_2065_ = leanh::lean_ctor_get(v_a_2061_, 0);
                    leanh::lean_inc(v_val_2065_);
                    leanh::lean_dec_ref_known(v_a_2061_, 1);
                    if v_isShared_2064_ == 0 {
                        leanh::lean_ctor_set(v___x_2063_, 0, v_val_2065_);
                        v___x_2067_ = v___x_2063_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
                        v___x_2067_ = v_reuseFailAlloc_2068_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2063_);
                    leanh::lean_dec(v_a_2061_);
                    leanh::lean_inc(v_mvarId_2045_);
                    v___x_2069_ = l_Lean_MVarId_congrImplies_x3f(
                        v_mvarId_2045_,
                        v_a_2046_,
                        v_a_2047_,
                        v_a_2048_,
                        v_a_2049_,
                    );
                    if leanh::lean_obj_tag(v___x_2069_) == 0 {
                        v_a_2070_ = leanh::lean_ctor_get(v___x_2069_, 0);
                        v_isSharedCheck_2081_ =
                            (!leanh::lean_is_exclusive(v___x_2069_)) as u8;
                        if v_isSharedCheck_2081_ == 0 {
                            v___x_2072_ = v___x_2069_;
                            v_isShared_2073_ = v_isSharedCheck_2081_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2070_);
                            leanh::lean_dec(v___x_2069_);
                            v___x_2072_ = leanh::lean_box(0);
                            v_isShared_2073_ = v_isSharedCheck_2081_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_2045_);
                        v_a_2082_ = leanh::lean_ctor_get(v___x_2069_, 0);
                        v_isSharedCheck_2089_ =
                            (!leanh::lean_is_exclusive(v___x_2069_)) as u8;
                        if v_isSharedCheck_2089_ == 0 {
                            v___x_2084_ = v___x_2069_;
                            v_isShared_2085_ = v_isSharedCheck_2089_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2082_);
                            leanh::lean_dec(v___x_2069_);
                            v___x_2084_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_2070_) == 1 {
                    leanh::lean_dec(v_mvarId_2045_);
                    v_val_2074_ = leanh::lean_ctor_get(v_a_2070_, 0);
                    leanh::lean_inc(v_val_2074_);
                    leanh::lean_dec_ref_known(v_a_2070_, 1);
                    if v_isShared_2073_ == 0 {
                        leanh::lean_ctor_set(v___x_2072_, 0, v_val_2074_);
                        v___x_2076_ = v___x_2072_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_val_2074_);
                        v___x_2076_ = v_reuseFailAlloc_2077_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2072_);
                    leanh::lean_dec(v_a_2070_);
                    v___x_2078_ = l_Lean_MVarId_congr_x3f___closed__1;
                    v___x_2079_ = leanh::lean_obj_once(
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
                    v_reuseFailAlloc_2088_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
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
                    v_reuseFailAlloc_2097_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
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
                    v_reuseFailAlloc_2106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
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
    mut v_mvarId_2108_: *mut leanh::LeanObject,
    mut v_a_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
    mut v_a_2112_: *mut leanh::LeanObject,
    mut v_a_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ =
        l_Lean_MVarId_congrCore(v_mvarId_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
    leanh::lean_dec(v_a_2112_);
    leanh::lean_dec_ref(v_a_2111_);
    leanh::lean_dec(v_a_2110_);
    leanh::lean_dec_ref(v_a_2109_);
    return v_res_2114_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
    mut v_closePost_2115_: u8,
    mut v_mvarId_2116_: *mut leanh::LeanObject,
    mut v_a_2117_: *mut leanh::LeanObject,
    mut v_a_2118_: *mut leanh::LeanObject,
    mut v_a_2119_: *mut leanh::LeanObject,
    mut v_a_2120_: *mut leanh::LeanObject,
    mut v_a_2121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transparency_2130_: u8 = 0;
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: u8 = 0;
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v_val_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v_a_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2129_ = l_Lean_Meta_Context_config(v_a_2118_);
                if v_closePost_2115_ == 0 {
                    leanh::lean_dec_ref(v___x_2129_);
                    state = 1;
                    continue;
                } else {
                    v_transparency_2130_ = leanh::lean_ctor_get_uint8(v___x_2129_, 9 as u32);
                    leanh::lean_dec_ref(v___x_2129_);
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
                            if leanh::lean_obj_tag(v___x_2135_) == 0 {
                                v_a_2136_ = leanh::lean_ctor_get(v___x_2135_, 0);
                                v_isSharedCheck_2152_ =
                                    (!leanh::lean_is_exclusive(v___x_2135_)) as u8;
                                if v_isSharedCheck_2152_ == 0 {
                                    v___x_2138_ = v___x_2135_;
                                    v_isShared_2139_ = v_isSharedCheck_2152_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2136_);
                                    leanh::lean_dec(v___x_2135_);
                                    v___x_2138_ = leanh::lean_box(0);
                                    v_isShared_2139_ = v_isSharedCheck_2152_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2153_ = leanh::lean_ctor_get(v___x_2135_, 0);
                                v_isSharedCheck_2160_ =
                                    (!leanh::lean_is_exclusive(v___x_2135_)) as u8;
                                if v_isSharedCheck_2160_ == 0 {
                                    v___x_2155_ = v___x_2135_;
                                    v_isShared_2156_ = v_isSharedCheck_2160_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2153_);
                                    leanh::lean_dec(v___x_2135_);
                                    v___x_2155_ = leanh::lean_box(0);
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
                v___x_2127_ = leanh::lean_box(0);
                v___x_2128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2128_, 0, v___x_2127_);
                return v___x_2128_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2136_) == 1 {
                    v_val_2140_ = leanh::lean_ctor_get(v_a_2136_, 0);
                    leanh::lean_inc(v_val_2140_);
                    leanh::lean_dec_ref_known(v_a_2136_, 1);
                    v___x_2141_ = lean_st_ref_take(v_a_2117_);
                    v___x_2142_ = lean_array_push(v___x_2141_, v_val_2140_);
                    v___x_2143_ = lean_st_ref_set(v_a_2117_, v___x_2142_);
                    v___x_2144_ = leanh::lean_box(0);
                    if v_isShared_2139_ == 0 {
                        leanh::lean_ctor_set(v___x_2138_, 0, v___x_2144_);
                        v___x_2146_ = v___x_2138_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
                        v___x_2146_ = v_reuseFailAlloc_2147_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2136_);
                    v___x_2148_ = leanh::lean_box(0);
                    if v_isShared_2139_ == 0 {
                        leanh::lean_ctor_set(v___x_2138_, 0, v___x_2148_);
                        v___x_2150_ = v___x_2138_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2151_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
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
                    v_reuseFailAlloc_2159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
    mut v_closePost_2161_: *mut leanh::LeanObject,
    mut v_mvarId_2162_: *mut leanh::LeanObject,
    mut v_a_2163_: *mut leanh::LeanObject,
    mut v_a_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
    mut v_a_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_closePost_boxed_2169_: u8 = 0;
    let mut v_res_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_closePost_boxed_2169_ = (leanh::lean_unbox(v_closePost_2161_) as u8);
    v_res_2170_ = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(
        v_closePost_boxed_2169_,
        v_mvarId_2162_,
        v_a_2163_,
        v_a_2164_,
        v_a_2165_,
        v_a_2166_,
        v_a_2167_,
    );
    leanh::lean_dec(v_a_2167_);
    leanh::lean_dec_ref(v_a_2166_);
    leanh::lean_dec(v_a_2165_);
    leanh::lean_dec_ref(v_a_2164_);
    leanh::lean_dec(v_a_2163_);
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
    mut v_n_2175_: *mut leanh::LeanObject,
    mut v_mvarId_2176_: *mut leanh::LeanObject,
    mut v_a_2177_: *mut leanh::LeanObject,
    mut v_a_2178_: *mut leanh::LeanObject,
    mut v_a_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2186_: u8 = 0;
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_a_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v_trackZetaDelta_2231_: u8 = 0;
    let mut v_zetaDeltaSet_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2238_: u8 = 0;
    let mut v_inTypeClassResolution_2239_: u8 = 0;
    let mut v_cacheInferType_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut v_config_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u64 = 0;
    let mut v___x_2245_: u64 = 0;
    let mut v___x_2246_: u64 = 0;
    let mut v___x_2247_: u64 = 0;
    let mut v___x_2248_: u64 = 0;
    let mut v_key_2249_: u64 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v_reuseFailAlloc_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    v_foApprox_2210_ = leanh::lean_ctor_get_uint8(v___x_2209_, 0 as u32);
                    v_ctxApprox_2211_ = leanh::lean_ctor_get_uint8(v___x_2209_, 1 as u32);
                    v_quasiPatternApprox_2212_ =
                        leanh::lean_ctor_get_uint8(v___x_2209_, 2 as u32);
                    v_constApprox_2213_ = leanh::lean_ctor_get_uint8(v___x_2209_, 3 as u32);
                    v_isDefEqStuckEx_2214_ =
                        leanh::lean_ctor_get_uint8(v___x_2209_, 4 as u32);
                    v_unificationHints_2215_ =
                        leanh::lean_ctor_get_uint8(v___x_2209_, 5 as u32);
                    v_proofIrrelevance_2216_ =
                        leanh::lean_ctor_get_uint8(v___x_2209_, 6 as u32);
                    v_assignSyntheticOpaque_2217_ =
                        leanh::lean_ctor_get_uint8(v___x_2209_, 7 as u32);
                    v_offsetCnstrs_2218_ = leanh::lean_ctor_get_uint8(v___x_2209_, 8 as u32);
                    v_etaStruct_2219_ = leanh::lean_ctor_get_uint8(v___x_2209_, 10 as u32);
                    v_univApprox_2220_ = leanh::lean_ctor_get_uint8(v___x_2209_, 11 as u32);
                    v_iota_2221_ = leanh::lean_ctor_get_uint8(v___x_2209_, 12 as u32);
                    v_beta_2222_ = leanh::lean_ctor_get_uint8(v___x_2209_, 13 as u32);
                    v_proj_2223_ = leanh::lean_ctor_get_uint8(v___x_2209_, 14 as u32);
                    v_zeta_2224_ = leanh::lean_ctor_get_uint8(v___x_2209_, 15 as u32);
                    v_zetaDelta_2225_ = leanh::lean_ctor_get_uint8(v___x_2209_, 16 as u32);
                    v_zetaUnused_2226_ = leanh::lean_ctor_get_uint8(v___x_2209_, 17 as u32);
                    v_zetaHave_2227_ = leanh::lean_ctor_get_uint8(v___x_2209_, 18 as u32);
                    v_isSharedCheck_2264_ = (!leanh::lean_is_exclusive(v___x_2209_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2229_ = v___x_2209_;
                        v_isShared_2230_ = v_isSharedCheck_2264_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2209_);
                        v___x_2229_ = leanh::lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2264_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_2185_ = leanh::lean_unsigned_to_nat(0);
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
                    leanh::lean_inc(v_val_2184_);
                    v___x_2188_ = leanh::lean_alloc_closure(
                        l_Lean_MVarId_congrCore___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___x_2188_, 0, v_val_2184_);
                    v___x_2189_ =
                        l_Lean_observing_x3f___at___00Lean_MVarId_congrImplies_x3f_spec__1___redArg(
                            v___x_2188_,
                            v_a_2178_,
                            v_a_2179_,
                            v_a_2180_,
                            v_a_2181_,
                        );
                    if leanh::lean_obj_tag(v___x_2189_) == 0 {
                        v_a_2190_ = leanh::lean_ctor_get(v___x_2189_, 0);
                        leanh::lean_inc(v_a_2190_);
                        leanh::lean_dec_ref_known(v___x_2189_, 1);
                        if leanh::lean_obj_tag(v_a_2190_) == 1 {
                            leanh::lean_dec(v_val_2184_);
                            v_val_2191_ = leanh::lean_ctor_get(v_a_2190_, 0);
                            leanh::lean_inc(v_val_2191_);
                            leanh::lean_dec_ref_known(v_a_2190_, 1);
                            v_one_2192_ = leanh::lean_unsigned_to_nat(1);
                            v_n_2193_ = lean_nat_sub(v_n_2175_, v_one_2192_);
                            v___x_2194_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(v_closePre_2173_, v_closePost_2174_, v_n_2193_, v_val_2191_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
                            leanh::lean_dec(v_n_2193_);
                            return v___x_2194_;
                        } else {
                            leanh::lean_dec(v_a_2190_);
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
                        leanh::lean_dec(v_val_2184_);
                        v_a_2196_ = leanh::lean_ctor_get(v___x_2189_, 0);
                        v_isSharedCheck_2203_ =
                            (!leanh::lean_is_exclusive(v___x_2189_)) as u8;
                        if v_isSharedCheck_2203_ == 0 {
                            v___x_2198_ = v___x_2189_;
                            v_isShared_2199_ = v_isSharedCheck_2203_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2196_);
                            leanh::lean_dec(v___x_2189_);
                            v___x_2198_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
                    v___x_2201_ = v_reuseFailAlloc_2202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2201_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_2205_) == 1 {
                    v_val_2206_ = leanh::lean_ctor_get(v_a_2205_, 0);
                    leanh::lean_inc(v_val_2206_);
                    leanh::lean_dec_ref_known(v_a_2205_, 1);
                    v_val_2184_ = v_val_2206_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2205_);
                    v___x_2207_ = leanh::lean_box(0);
                    v___x_2208_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2208_, 0, v___x_2207_);
                    return v___x_2208_;
                }
            }
            5 => {
                v_trackZetaDelta_2231_ = leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2232_ = leanh::lean_ctor_get(v_a_2178_, 1);
                v_lctx_2233_ = leanh::lean_ctor_get(v_a_2178_, 2);
                v_localInstances_2234_ = leanh::lean_ctor_get(v_a_2178_, 3);
                v_defEqCtx_x3f_2235_ = leanh::lean_ctor_get(v_a_2178_, 4);
                v_synthPendingDepth_2236_ = leanh::lean_ctor_get(v_a_2178_, 5);
                v_canUnfold_x3f_2237_ = leanh::lean_ctor_get(v_a_2178_, 6);
                v_univApprox_2238_ = leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2239_ = leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2240_ = leanh::lean_ctor_get_uint8(
                    v_a_2178_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2241_ = 2;
                if v_isShared_2230_ == 0 {
                    v_config_2243_ = v___x_2229_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        0 as u32,
                        v_foApprox_2210_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        1 as u32,
                        v_ctxApprox_2211_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        2 as u32,
                        v_quasiPatternApprox_2212_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        3 as u32,
                        v_constApprox_2213_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        4 as u32,
                        v_isDefEqStuckEx_2214_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        5 as u32,
                        v_unificationHints_2215_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        6 as u32,
                        v_proofIrrelevance_2216_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        7 as u32,
                        v_assignSyntheticOpaque_2217_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        8 as u32,
                        v_offsetCnstrs_2218_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        10 as u32,
                        v_etaStruct_2219_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        11 as u32,
                        v_univApprox_2220_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        12 as u32,
                        v_iota_2221_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        13 as u32,
                        v_beta_2222_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        14 as u32,
                        v_proj_2223_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        15 as u32,
                        v_zeta_2224_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        16 as u32,
                        v_zetaDelta_2225_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        17 as u32,
                        v_zetaUnused_2226_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_2243_, 9 as u32, v___x_2241_);
                v___x_2244_ = l_Lean_Meta_Context_configKey(v_a_2178_);
                v___x_2245_ = 3u64;
                v___x_2246_ = lean_uint64_shift_right(v___x_2244_, v___x_2245_);
                v___x_2247_ = lean_uint64_shift_left(v___x_2246_, v___x_2245_);
                v___x_2248_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0);
                v_key_2249_ = lean_uint64_lor(v___x_2247_, v___x_2248_);
                v___x_2250_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2250_, 0, v_config_2243_);
                leanh::lean_ctor_set_uint64(
                    v___x_2250_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2249_,
                );
                leanh::lean_inc(v_canUnfold_x3f_2237_);
                leanh::lean_inc(v_synthPendingDepth_2236_);
                leanh::lean_inc(v_defEqCtx_x3f_2235_);
                leanh::lean_inc_ref(v_localInstances_2234_);
                leanh::lean_inc_ref(v_lctx_2233_);
                leanh::lean_inc(v_zetaDeltaSet_2232_);
                v___x_2251_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                leanh::lean_ctor_set(v___x_2251_, 1, v_zetaDeltaSet_2232_);
                leanh::lean_ctor_set(v___x_2251_, 2, v_lctx_2233_);
                leanh::lean_ctor_set(v___x_2251_, 3, v_localInstances_2234_);
                leanh::lean_ctor_set(v___x_2251_, 4, v_defEqCtx_x3f_2235_);
                leanh::lean_ctor_set(v___x_2251_, 5, v_synthPendingDepth_2236_);
                leanh::lean_ctor_set(v___x_2251_, 6, v_canUnfold_x3f_2237_);
                leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2231_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2238_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2239_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2251_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2240_,
                );
                v___x_2252_ = l_Lean_MVarId_congrPre(
                    v_mvarId_2176_,
                    v___x_2251_,
                    v_a_2179_,
                    v_a_2180_,
                    v_a_2181_,
                );
                leanh::lean_dec_ref_known(v___x_2251_, 7);
                if leanh::lean_obj_tag(v___x_2252_) == 0 {
                    v_a_2253_ = leanh::lean_ctor_get(v___x_2252_, 0);
                    leanh::lean_inc(v_a_2253_);
                    leanh::lean_dec_ref_known(v___x_2252_, 1);
                    v_a_2205_ = v_a_2253_;
                    state = 4;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v___x_2252_) == 0 {
                        v_a_2254_ = leanh::lean_ctor_get(v___x_2252_, 0);
                        leanh::lean_inc(v_a_2254_);
                        leanh::lean_dec_ref_known(v___x_2252_, 1);
                        v_a_2205_ = v_a_2254_;
                        state = 4;
                        continue;
                    } else {
                        v_a_2255_ = leanh::lean_ctor_get(v___x_2252_, 0);
                        v_isSharedCheck_2262_ =
                            (!leanh::lean_is_exclusive(v___x_2252_)) as u8;
                        if v_isSharedCheck_2262_ == 0 {
                            v___x_2257_ = v___x_2252_;
                            v_isShared_2258_ = v_isSharedCheck_2262_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2255_);
                            leanh::lean_dec(v___x_2252_);
                            v___x_2257_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
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
    mut v_n_2267_: *mut leanh::LeanObject,
    mut v_as_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
    mut v___y_2270_: *mut leanh::LeanObject,
    mut v___y_2271_: *mut leanh::LeanObject,
    mut v___y_2272_: *mut leanh::LeanObject,
    mut v___y_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_2268_) == 0 {
                    v___x_2275_ = leanh::lean_box(0);
                    v___x_2276_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
                    return v___x_2276_;
                } else {
                    v_head_2277_ = leanh::lean_ctor_get(v_as_2268_, 0);
                    leanh::lean_inc(v_head_2277_);
                    v_tail_2278_ = leanh::lean_ctor_get(v_as_2268_, 1);
                    leanh::lean_inc(v_tail_2278_);
                    leanh::lean_dec_ref_known(v_as_2268_, 2);
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
                    if leanh::lean_obj_tag(v___x_2279_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2279_, 1);
                        v_as_2268_ = v_tail_2278_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tail_2278_);
                        return v___x_2279_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(
    mut v_closePre_2281_: *mut leanh::LeanObject,
    mut v_closePost_2282_: *mut leanh::LeanObject,
    mut v_n_2283_: *mut leanh::LeanObject,
    mut v_as_2284_: *mut leanh::LeanObject,
    mut v___y_2285_: *mut leanh::LeanObject,
    mut v___y_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
    mut v___y_2290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_closePre_boxed_2291_: u8 = 0;
    let mut v_closePost_boxed_2292_: u8 = 0;
    let mut v_res_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2291_ = (leanh::lean_unbox(v_closePre_2281_) as u8);
    v_closePost_boxed_2292_ = (leanh::lean_unbox(v_closePost_2282_) as u8);
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
    leanh::lean_dec(v___y_2289_);
    leanh::lean_dec_ref(v___y_2288_);
    leanh::lean_dec(v___y_2287_);
    leanh::lean_dec_ref(v___y_2286_);
    leanh::lean_dec(v___y_2285_);
    leanh::lean_dec(v_n_2283_);
    return v_res_2293_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(
    mut v_closePre_2294_: *mut leanh::LeanObject,
    mut v_closePost_2295_: *mut leanh::LeanObject,
    mut v_n_2296_: *mut leanh::LeanObject,
    mut v_mvarId_2297_: *mut leanh::LeanObject,
    mut v_a_2298_: *mut leanh::LeanObject,
    mut v_a_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
    mut v_a_2301_: *mut leanh::LeanObject,
    mut v_a_2302_: *mut leanh::LeanObject,
    mut v_a_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_closePre_boxed_2304_: u8 = 0;
    let mut v_closePost_boxed_2305_: u8 = 0;
    let mut v_res_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2304_ = (leanh::lean_unbox(v_closePre_2294_) as u8);
    v_closePost_boxed_2305_ = (leanh::lean_unbox(v_closePost_2295_) as u8);
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
    leanh::lean_dec(v_a_2302_);
    leanh::lean_dec_ref(v_a_2301_);
    leanh::lean_dec(v_a_2300_);
    leanh::lean_dec_ref(v_a_2299_);
    leanh::lean_dec(v_a_2298_);
    leanh::lean_dec(v_n_2296_);
    return v_res_2306_;
}
pub unsafe fn l_Lean_MVarId_congrN(
    mut v_mvarId_2309_: *mut leanh::LeanObject,
    mut v_depth_2310_: *mut leanh::LeanObject,
    mut v_closePre_2311_: u8,
    mut v_closePost_2312_: u8,
    mut v_a_2313_: *mut leanh::LeanObject,
    mut v_a_2314_: *mut leanh::LeanObject,
    mut v_a_2315_: *mut leanh::LeanObject,
    mut v_a_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_unused_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2334_: u8 = 0;
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2320_) == 0 {
                    v_isSharedCheck_2329_ = (!leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v_unused_2330_ = leanh::lean_ctor_get(v___x_2320_, 0);
                        leanh::lean_dec(v_unused_2330_);
                        v___x_2322_ = v___x_2320_;
                        v_isShared_2323_ = v_isSharedCheck_2329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2320_);
                        v___x_2322_ = leanh::lean_box(0);
                        v_isShared_2323_ = v_isSharedCheck_2329_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2319_);
                    v_a_2331_ = leanh::lean_ctor_get(v___x_2320_, 0);
                    v_isSharedCheck_2338_ = (!leanh::lean_is_exclusive(v___x_2320_)) as u8;
                    if v_isSharedCheck_2338_ == 0 {
                        v___x_2333_ = v___x_2320_;
                        v_isShared_2334_ = v_isSharedCheck_2338_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2331_);
                        leanh::lean_dec(v___x_2320_);
                        v___x_2333_ = leanh::lean_box(0);
                        v_isShared_2334_ = v_isSharedCheck_2338_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2324_ = lean_st_ref_get(v___x_2319_);
                leanh::lean_dec(v___x_2319_);
                v___x_2325_ = lean_array_to_list(v___x_2324_);
                if v_isShared_2323_ == 0 {
                    leanh::lean_ctor_set(v___x_2322_, 0, v___x_2325_);
                    v___x_2327_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
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
                    v_reuseFailAlloc_2337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
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
    mut v_mvarId_2339_: *mut leanh::LeanObject,
    mut v_depth_2340_: *mut leanh::LeanObject,
    mut v_closePre_2341_: *mut leanh::LeanObject,
    mut v_closePost_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_closePre_boxed_2348_: u8 = 0;
    let mut v_closePost_boxed_2349_: u8 = 0;
    let mut v_res_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_closePre_boxed_2348_ = (leanh::lean_unbox(v_closePre_2341_) as u8);
    v_closePost_boxed_2349_ = (leanh::lean_unbox(v_closePost_2342_) as u8);
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
    leanh::lean_dec(v_a_2346_);
    leanh::lean_dec_ref(v_a_2345_);
    leanh::lean_dec(v_a_2344_);
    leanh::lean_dec_ref(v_a_2343_);
    leanh::lean_dec(v_depth_2340_);
    return v_res_2350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Congr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Congr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Congr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_CongrTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Congr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Congr(builtin);
}