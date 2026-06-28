// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.Basic Std.Tactic.BVDecide.Normalize.BitVec
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr6};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpTheoremsArray_addTheorem, l_Lean_Meta_simpGlobalConfig,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
use crate::r#gen::Std::Tactic::BVDecide::Normalize::BitVec::{
    initialize_Std_Tactic_BVDecide_Normalize_BitVec,
    runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0_value:
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
        109, 117, 108, 95, 98, 101, 113, 95, 109, 117, 108, 95, 115, 104, 111, 114, 116, 95, 99,
        105, 114, 99, 117, 105, 116, 95, 114, 105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [78, 111, 114, 109, 97, 108, 105, 122, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        109, 117, 108, 95, 98, 101, 113, 95, 109, 117, 108, 95, 115, 104, 111, 114, 116, 95, 99,
        105, 114, 99, 117, 105, 116, 95, 108, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        5139300886809190733 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        17363264175708149920 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        1678646150249543785 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        13924334440726705414 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        10870596837306544181 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        1 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        115, 104, 111, 114, 116, 67, 105, 114, 99, 117, 105, 116, 80, 97, 115, 115, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        2044961249380779309 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(
    mut v_x_286_: *mut crate::leanh::LeanObject,
    mut v___y_287_: *mut crate::leanh::LeanObject,
    mut v___y_288_: *mut crate::leanh::LeanObject,
    mut v___y_289_: *mut crate::leanh::LeanObject,
    mut v___y_290_: *mut crate::leanh::LeanObject,
    mut v___y_291_: *mut crate::leanh::LeanObject,
    mut v___y_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_288_);
    crate::leanh::lean_inc_ref(v___y_287_);
    v___x_294_ = crate::leanh::lean_apply_7(
        v_x_286_,
        v___y_287_,
        v___y_288_,
        v___y_289_,
        v___y_290_,
        v___y_291_,
        v___y_292_,
        crate::leanh::lean_box(0),
    );
    return v___x_294_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(
    mut v_x_295_: *mut crate::leanh::LeanObject,
    mut v___y_296_: *mut crate::leanh::LeanObject,
    mut v___y_297_: *mut crate::leanh::LeanObject,
    mut v___y_298_: *mut crate::leanh::LeanObject,
    mut v___y_299_: *mut crate::leanh::LeanObject,
    mut v___y_300_: *mut crate::leanh::LeanObject,
    mut v___y_301_: *mut crate::leanh::LeanObject,
    mut v___y_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
    crate::leanh::lean_dec(v___y_297_);
    crate::leanh::lean_dec_ref(v___y_296_);
    return v_res_303_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(
    mut v_mvarId_304_: *mut crate::leanh::LeanObject,
    mut v_x_305_: *mut crate::leanh::LeanObject,
    mut v___y_306_: *mut crate::leanh::LeanObject,
    mut v___y_307_: *mut crate::leanh::LeanObject,
    mut v___y_308_: *mut crate::leanh::LeanObject,
    mut v___y_309_: *mut crate::leanh::LeanObject,
    mut v___y_310_: *mut crate::leanh::LeanObject,
    mut v___y_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_307_);
                crate::leanh::lean_inc_ref(v___y_306_);
                v___f_313_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_313_, 0, v_x_305_);
                crate::leanh::lean_closure_set(v___f_313_, 1, v___y_306_);
                crate::leanh::lean_closure_set(v___f_313_, 2, v___y_307_);
                v___x_314_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_304_,
                    v___f_313_,
                    v___y_308_,
                    v___y_309_,
                    v___y_310_,
                    v___y_311_,
                );
                if crate::leanh::lean_obj_tag(v___x_314_) == 0 {
                    return v___x_314_;
                } else {
                    v_a_315_ = crate::leanh::lean_ctor_get(v___x_314_, 0);
                    v_isSharedCheck_322_ = (!crate::leanh::lean_is_exclusive(v___x_314_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_317_ = v___x_314_;
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_315_);
                        crate::leanh::lean_dec(v___x_314_);
                        v___x_317_ = crate::leanh::lean_box(0);
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_318_ == 0 {
                    v___x_320_ = v___x_317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
                    v___x_320_ = v_reuseFailAlloc_321_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_320_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___boxed(
    mut v_mvarId_323_: *mut crate::leanh::LeanObject,
    mut v_x_324_: *mut crate::leanh::LeanObject,
    mut v___y_325_: *mut crate::leanh::LeanObject,
    mut v___y_326_: *mut crate::leanh::LeanObject,
    mut v___y_327_: *mut crate::leanh::LeanObject,
    mut v___y_328_: *mut crate::leanh::LeanObject,
    mut v___y_329_: *mut crate::leanh::LeanObject,
    mut v___y_330_: *mut crate::leanh::LeanObject,
    mut v___y_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_323_, v_x_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
    crate::leanh::lean_dec(v___y_330_);
    crate::leanh::lean_dec_ref(v___y_329_);
    crate::leanh::lean_dec(v___y_328_);
    crate::leanh::lean_dec_ref(v___y_327_);
    crate::leanh::lean_dec(v___y_326_);
    crate::leanh::lean_dec_ref(v___y_325_);
    return v_res_332_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(
    mut v_00_u03b1_333_: *mut crate::leanh::LeanObject,
    mut v_mvarId_334_: *mut crate::leanh::LeanObject,
    mut v_x_335_: *mut crate::leanh::LeanObject,
    mut v___y_336_: *mut crate::leanh::LeanObject,
    mut v___y_337_: *mut crate::leanh::LeanObject,
    mut v___y_338_: *mut crate::leanh::LeanObject,
    mut v___y_339_: *mut crate::leanh::LeanObject,
    mut v___y_340_: *mut crate::leanh::LeanObject,
    mut v___y_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_334_, v_x_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
    return v___x_343_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___boxed(
    mut v_00_u03b1_344_: *mut crate::leanh::LeanObject,
    mut v_mvarId_345_: *mut crate::leanh::LeanObject,
    mut v_x_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
    mut v___y_348_: *mut crate::leanh::LeanObject,
    mut v___y_349_: *mut crate::leanh::LeanObject,
    mut v___y_350_: *mut crate::leanh::LeanObject,
    mut v___y_351_: *mut crate::leanh::LeanObject,
    mut v___y_352_: *mut crate::leanh::LeanObject,
    mut v___y_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(v_00_u03b1_344_, v_mvarId_345_, v_x_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
    crate::leanh::lean_dec(v___y_352_);
    crate::leanh::lean_dec_ref(v___y_351_);
    crate::leanh::lean_dec(v___y_350_);
    crate::leanh::lean_dec_ref(v___y_349_);
    crate::leanh::lean_dec(v___y_348_);
    crate::leanh::lean_dec_ref(v___y_347_);
    return v_res_354_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_356_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_357_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1,
    );
    v___x_358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_358_, 0, v___x_357_);
    return v___x_358_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
    v___x_361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_361_, 0, v___x_360_);
    return v___x_361_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(
    mut v_theorems_362_: *mut crate::leanh::LeanObject,
    mut v___x_363_: *mut crate::leanh::LeanObject,
    mut v___x_364_: *mut crate::leanh::LeanObject,
    mut v___x_365_: *mut crate::leanh::LeanObject,
    mut v___x_366_: *mut crate::leanh::LeanObject,
    mut v___x_367_: *mut crate::leanh::LeanObject,
    mut v___x_368_: *mut crate::leanh::LeanObject,
    mut v___x_369_: *mut crate::leanh::LeanObject,
    mut v___x_370_: *mut crate::leanh::LeanObject,
    mut v___x_371_: u8,
    mut v___x_372_: u8,
    mut v___x_373_: *mut crate::leanh::LeanObject,
    mut v___x_374_: *mut crate::leanh::LeanObject,
    mut v_goal_375_: *mut crate::leanh::LeanObject,
    mut v___y_376_: *mut crate::leanh::LeanObject,
    mut v___y_377_: *mut crate::leanh::LeanObject,
    mut v___y_378_: *mut crate::leanh::LeanObject,
    mut v___y_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: u8 = 0;
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: usize = 0;
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_417_: u8 = 0;
    let mut v_fst_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_422_: u8 = 0;
    let mut v_snd_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut v_a_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_438_: u8 = 0;
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut v_a_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut v_a_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_a_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_a_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_a_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_365_);
                v___x_383_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                    v_theorems_362_,
                    v___x_363_,
                    v___x_364_,
                    v___x_365_,
                    v___y_378_,
                    v___y_379_,
                    v___y_380_,
                    v___y_381_,
                );
                if crate::leanh::lean_obj_tag(v___x_383_) == 0 {
                    v_a_384_ = crate::leanh::lean_ctor_get(v___x_383_, 0);
                    crate::leanh::lean_inc(v_a_384_);
                    crate::leanh::lean_dec_ref_known(v___x_383_, 1);
                    v___x_385_ =
                        l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0;
                    v___x_386_ = l_Lean_Name_mkStr6(
                        v___x_366_, v___x_367_, v___x_368_, v___x_369_, v___x_370_, v___x_385_,
                    );
                    crate::leanh::lean_inc(v___x_386_);
                    v___x_387_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_387_, 0, v___x_386_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_371_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                        v___x_372_,
                    );
                    v___x_388_ = l_Lean_mkConst(v___x_386_, v___x_373_);
                    v___x_389_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                        v_a_384_, v___x_387_, v___x_388_, v___x_365_, v___y_378_, v___y_379_,
                        v___y_380_, v___y_381_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_389_) == 0 {
                        v_a_390_ = crate::leanh::lean_ctor_get(v___x_389_, 0);
                        crate::leanh::lean_inc(v_a_390_);
                        crate::leanh::lean_dec_ref_known(v___x_389_, 1);
                        v___x_391_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_381_);
                        if crate::leanh::lean_obj_tag(v___x_391_) == 0 {
                            v_a_392_ = crate::leanh::lean_ctor_get(v___x_391_, 0);
                            crate::leanh::lean_inc(v_a_392_);
                            crate::leanh::lean_dec_ref_known(v___x_391_, 1);
                            v_maxSteps_393_ = crate::leanh::lean_ctor_get(v___y_376_, 1);
                            v___x_394_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_395_ = 0;
                            v___x_396_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_maxSteps_393_);
                            v___x_397_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                            crate::leanh::lean_ctor_set(v___x_397_, 0, v_maxSteps_393_);
                            crate::leanh::lean_ctor_set(v___x_397_, 1, v___x_394_);
                            crate::leanh::lean_ctor_set(v___x_397_, 2, v___x_396_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6)
                                    as u32,
                                v___x_395_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25)
                                    as u32,
                                v___x_371_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27)
                                    as u32,
                                v___x_372_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28)
                                    as u32,
                                v___x_372_,
                            );
                            v___x_398_ = l_Lean_Options_empty;
                            v___x_399_ = l_Lean_Meta_Simp_mkContext___redArg(
                                v___x_397_, v_a_390_, v_a_392_, v___x_398_, v___y_378_, v___y_380_,
                                v___y_381_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_399_) == 0 {
                                v_a_400_ = crate::leanh::lean_ctor_get(v___x_399_, 0);
                                crate::leanh::lean_inc(v_a_400_);
                                crate::leanh::lean_dec_ref_known(v___x_399_, 1);
                                v___x_401_ = l_Lean_Meta_getPropHyps(
                                    v___y_378_, v___y_379_, v___y_380_, v___y_381_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_401_) == 0 {
                                    v_a_402_ = crate::leanh::lean_ctor_get(v___x_401_, 0);
                                    crate::leanh::lean_inc(v_a_402_);
                                    crate::leanh::lean_dec_ref_known(v___x_401_, 1);
                                    v___x_403_ = lean_mk_empty_array_with_capacity(v___x_374_);
                                    v___x_404_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2);
                                    crate::leanh::lean_inc_n(v___x_374_, 2);
                                    v___x_405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
                                    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_374_);
                                    v___x_406_ = crate::leanh::lean_unsigned_to_nat(32);
                                    v___x_407_ = lean_mk_empty_array_with_capacity(v___x_406_);
                                    v___x_408_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3);
                                    v___x_409_ = 5usize;
                                    v___x_410_ = crate::leanh::lean_alloc_ctor(
                                        0,
                                        4,
                                        (core::mem::size_of::<usize>() * 1) as u32,
                                    );
                                    crate::leanh::lean_ctor_set(v___x_410_, 0, v___x_408_);
                                    crate::leanh::lean_ctor_set(v___x_410_, 1, v___x_407_);
                                    crate::leanh::lean_ctor_set(v___x_410_, 2, v___x_374_);
                                    crate::leanh::lean_ctor_set(v___x_410_, 3, v___x_374_);
                                    crate::leanh::lean_ctor_set_usize(v___x_410_, 4, v___x_409_);
                                    v___x_411_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_411_, 0, v___x_404_);
                                    crate::leanh::lean_ctor_set(v___x_411_, 1, v___x_404_);
                                    crate::leanh::lean_ctor_set(v___x_411_, 2, v___x_404_);
                                    crate::leanh::lean_ctor_set(v___x_411_, 3, v___x_410_);
                                    v___x_412_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_412_, 0, v___x_405_);
                                    crate::leanh::lean_ctor_set(v___x_412_, 1, v___x_411_);
                                    v___x_413_ = l_Lean_Meta_simpGoal(
                                        v_goal_375_,
                                        v_a_400_,
                                        v___x_403_,
                                        v___x_396_,
                                        v___x_371_,
                                        v_a_402_,
                                        v___x_412_,
                                        v___y_378_,
                                        v___y_379_,
                                        v___y_380_,
                                        v___y_381_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_413_) == 0 {
                                        v_a_414_ = crate::leanh::lean_ctor_get(v___x_413_, 0);
                                        v_isSharedCheck_434_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_413_)) as u8;
                                        if v_isSharedCheck_434_ == 0 {
                                            v___x_416_ = v___x_413_;
                                            v_isShared_417_ = v_isSharedCheck_434_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_414_);
                                            crate::leanh::lean_dec(v___x_413_);
                                            v___x_416_ = crate::leanh::lean_box(0);
                                            v_isShared_417_ = v_isSharedCheck_434_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v_a_435_ = crate::leanh::lean_ctor_get(v___x_413_, 0);
                                        v_isSharedCheck_442_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_413_)) as u8;
                                        if v_isSharedCheck_442_ == 0 {
                                            v___x_437_ = v___x_413_;
                                            v_isShared_438_ = v_isSharedCheck_442_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_435_);
                                            crate::leanh::lean_dec(v___x_413_);
                                            v___x_437_ = crate::leanh::lean_box(0);
                                            v_isShared_438_ = v_isSharedCheck_442_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_400_);
                                    crate::leanh::lean_dec(v_goal_375_);
                                    crate::leanh::lean_dec(v___x_374_);
                                    v_a_443_ = crate::leanh::lean_ctor_get(v___x_401_, 0);
                                    v_isSharedCheck_450_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_401_)) as u8;
                                    if v_isSharedCheck_450_ == 0 {
                                        v___x_445_ = v___x_401_;
                                        v_isShared_446_ = v_isSharedCheck_450_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_443_);
                                        crate::leanh::lean_dec(v___x_401_);
                                        v___x_445_ = crate::leanh::lean_box(0);
                                        v_isShared_446_ = v_isSharedCheck_450_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_goal_375_);
                                crate::leanh::lean_dec(v___x_374_);
                                v_a_451_ = crate::leanh::lean_ctor_get(v___x_399_, 0);
                                v_isSharedCheck_458_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_399_)) as u8;
                                if v_isSharedCheck_458_ == 0 {
                                    v___x_453_ = v___x_399_;
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_451_);
                                    crate::leanh::lean_dec(v___x_399_);
                                    v___x_453_ = crate::leanh::lean_box(0);
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_390_);
                            crate::leanh::lean_dec(v_goal_375_);
                            crate::leanh::lean_dec(v___x_374_);
                            v_a_459_ = crate::leanh::lean_ctor_get(v___x_391_, 0);
                            v_isSharedCheck_466_ =
                                (!crate::leanh::lean_is_exclusive(v___x_391_)) as u8;
                            if v_isSharedCheck_466_ == 0 {
                                v___x_461_ = v___x_391_;
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_459_);
                                crate::leanh::lean_dec(v___x_391_);
                                v___x_461_ = crate::leanh::lean_box(0);
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_goal_375_);
                        crate::leanh::lean_dec(v___x_374_);
                        v_a_467_ = crate::leanh::lean_ctor_get(v___x_389_, 0);
                        v_isSharedCheck_474_ = (!crate::leanh::lean_is_exclusive(v___x_389_)) as u8;
                        if v_isSharedCheck_474_ == 0 {
                            v___x_469_ = v___x_389_;
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_467_);
                            crate::leanh::lean_dec(v___x_389_);
                            v___x_469_ = crate::leanh::lean_box(0);
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_375_);
                    crate::leanh::lean_dec(v___x_374_);
                    crate::leanh::lean_dec(v___x_373_);
                    crate::leanh::lean_dec_ref(v___x_370_);
                    crate::leanh::lean_dec_ref(v___x_369_);
                    crate::leanh::lean_dec_ref(v___x_368_);
                    crate::leanh::lean_dec_ref(v___x_367_);
                    crate::leanh::lean_dec_ref(v___x_366_);
                    crate::leanh::lean_dec_ref(v___x_365_);
                    v_a_475_ = crate::leanh::lean_ctor_get(v___x_383_, 0);
                    v_isSharedCheck_482_ = (!crate::leanh::lean_is_exclusive(v___x_383_)) as u8;
                    if v_isSharedCheck_482_ == 0 {
                        v___x_477_ = v___x_383_;
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_475_);
                        crate::leanh::lean_dec(v___x_383_);
                        v___x_477_ = crate::leanh::lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_418_ = crate::leanh::lean_ctor_get(v_a_414_, 0);
                crate::leanh::lean_inc(v_fst_418_);
                crate::leanh::lean_dec(v_a_414_);
                if crate::leanh::lean_obj_tag(v_fst_418_) == 1 {
                    v_val_419_ = crate::leanh::lean_ctor_get(v_fst_418_, 0);
                    v_isSharedCheck_430_ = (!crate::leanh::lean_is_exclusive(v_fst_418_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_421_ = v_fst_418_;
                        v_isShared_422_ = v_isSharedCheck_430_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_419_);
                        crate::leanh::lean_dec(v_fst_418_);
                        v___x_421_ = crate::leanh::lean_box(0);
                        v_isShared_422_ = v_isSharedCheck_430_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_418_);
                    if v_isShared_417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_396_);
                        v___x_432_ = v___x_416_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_396_);
                        v___x_432_ = v_reuseFailAlloc_433_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_423_ = crate::leanh::lean_ctor_get(v_val_419_, 1);
                crate::leanh::lean_inc(v_snd_423_);
                crate::leanh::lean_dec(v_val_419_);
                if v_isShared_422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_421_, 0, v_snd_423_);
                    v___x_425_ = v___x_421_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_snd_423_);
                    v___x_425_ = v_reuseFailAlloc_429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_416_, 0, v___x_425_);
                    v___x_427_ = v___x_416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
                    v___x_427_ = v_reuseFailAlloc_428_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_427_;
            }
            5 => {
                return v___x_432_;
            }
            6 => {
                if v_isShared_438_ == 0 {
                    v___x_440_ = v___x_437_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_440_;
            }
            8 => {
                if v_isShared_446_ == 0 {
                    v___x_448_ = v___x_445_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
                    v___x_448_ = v_reuseFailAlloc_449_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_448_;
            }
            10 => {
                if v_isShared_454_ == 0 {
                    v___x_456_ = v___x_453_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
                    v___x_456_ = v_reuseFailAlloc_457_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_456_;
            }
            12 => {
                if v_isShared_462_ == 0 {
                    v___x_464_ = v___x_461_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
                    v___x_464_ = v_reuseFailAlloc_465_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_464_;
            }
            14 => {
                if v_isShared_470_ == 0 {
                    v___x_472_ = v___x_469_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
                    v___x_472_ = v_reuseFailAlloc_473_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_472_;
            }
            16 => {
                if v_isShared_478_ == 0 {
                    v___x_480_ = v___x_477_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
                    v___x_480_ = v_reuseFailAlloc_481_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_theorems_483_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_484_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_485_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_486_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_487_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_488_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_489_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_490_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_491_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_492_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_493_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_494_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_495_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_goal_496_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_497_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_498_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_499_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_500_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_501_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_502_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_503_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_5256__boxed_504_: u8 = 0;
    let mut v___x_5257__boxed_505_: u8 = 0;
    let mut v_res_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5256__boxed_504_ = (crate::leanh::lean_unbox(v___x_492_) as u8);
    v___x_5257__boxed_505_ = (crate::leanh::lean_unbox(v___x_493_) as u8);
    v_res_506_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(
        v_theorems_483_,
        v___x_484_,
        v___x_485_,
        v___x_486_,
        v___x_487_,
        v___x_488_,
        v___x_489_,
        v___x_490_,
        v___x_491_,
        v___x_5256__boxed_504_,
        v___x_5257__boxed_505_,
        v___x_494_,
        v___x_495_,
        v_goal_496_,
        v___y_497_,
        v___y_498_,
        v___y_499_,
        v___y_500_,
        v___y_501_,
        v___y_502_,
    );
    crate::leanh::lean_dec(v___y_502_);
    crate::leanh::lean_dec_ref(v___y_501_);
    crate::leanh::lean_dec(v___y_500_);
    crate::leanh::lean_dec_ref(v___y_499_);
    crate::leanh::lean_dec(v___y_498_);
    crate::leanh::lean_dec_ref(v___y_497_);
    return v_res_506_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = crate::leanh::lean_box(0);
    v___x_527_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7;
    v___x_528_ = l_Lean_mkConst(v___x_527_, v___x_526_);
    return v___x_528_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(
    mut v_goal_529_: *mut crate::leanh::LeanObject,
    mut v___y_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
    mut v___y_533_: *mut crate::leanh::LeanObject,
    mut v___y_534_: *mut crate::leanh::LeanObject,
    mut v___y_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_theorems_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = crate::leanh::lean_unsigned_to_nat(0);
    v_theorems_538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0;
    v___x_539_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1;
    v___x_540_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2;
    v___x_541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3;
    v___x_542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4;
    v___x_543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5;
    v___x_544_ = 1;
    v___x_545_ = 0;
    v___x_546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8;
    v___x_547_ = crate::leanh::lean_box(0);
    v___x_548_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9,
    );
    v___x_549_ = l_Lean_Meta_simpGlobalConfig;
    v___x_550_ = crate::leanh::lean_box((v___x_544_) as usize);
    v___x_551_ = crate::leanh::lean_box((v___x_545_) as usize);
    crate::leanh::lean_inc(v_goal_529_);
    v___f_552_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed
            as *mut core::ffi::c_void,
        21,
        14,
    );
    crate::leanh::lean_closure_set(v___f_552_, 0, v_theorems_538_);
    crate::leanh::lean_closure_set(v___f_552_, 1, v___x_546_);
    crate::leanh::lean_closure_set(v___f_552_, 2, v___x_548_);
    crate::leanh::lean_closure_set(v___f_552_, 3, v___x_549_);
    crate::leanh::lean_closure_set(v___f_552_, 4, v___x_539_);
    crate::leanh::lean_closure_set(v___f_552_, 5, v___x_540_);
    crate::leanh::lean_closure_set(v___f_552_, 6, v___x_541_);
    crate::leanh::lean_closure_set(v___f_552_, 7, v___x_542_);
    crate::leanh::lean_closure_set(v___f_552_, 8, v___x_543_);
    crate::leanh::lean_closure_set(v___f_552_, 9, v___x_550_);
    crate::leanh::lean_closure_set(v___f_552_, 10, v___x_551_);
    crate::leanh::lean_closure_set(v___f_552_, 11, v___x_547_);
    crate::leanh::lean_closure_set(v___f_552_, 12, v___x_537_);
    crate::leanh::lean_closure_set(v___f_552_, 13, v_goal_529_);
    v___x_553_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_goal_529_, v___f_552_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
    return v___x_553_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed(
    mut v_goal_554_: *mut crate::leanh::LeanObject,
    mut v___y_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(
        v_goal_554_,
        v___y_555_,
        v___y_556_,
        v___y_557_,
        v___y_558_,
        v___y_559_,
        v___y_560_,
    );
    crate::leanh::lean_dec(v___y_560_);
    crate::leanh::lean_dec_ref(v___y_559_);
    crate::leanh::lean_dec(v___y_558_);
    crate::leanh::lean_dec_ref(v___y_557_);
    crate::leanh::lean_dec(v___y_556_);
    crate::leanh::lean_dec_ref(v___y_555_);
    return v_res_562_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
}
