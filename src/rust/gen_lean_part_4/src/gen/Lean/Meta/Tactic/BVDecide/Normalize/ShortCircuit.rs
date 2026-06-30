// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.Basic Std.Tactic.BVDecide.Normalize.BitVec
use crate::ffi::lean_mk_empty_array_with_capacity;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr6;
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
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0_value:
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
        109, 117, 108, 95, 98, 101, 113, 95, 109, 117, 108, 95, 115, 104, 111, 114, 116, 95, 99,
        105, 114, 99, 117, 105, 116, 95, 114, 105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value:
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
    m_data: [66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value:
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
        109, 117, 108, 95, 98, 101, 113, 95, 109, 117, 108, 95, 115, 104, 111, 114, 116, 95, 99,
        105, 114, 99, 117, 105, 116, 95, 108, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        5139300886809190733 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3_value
        ) as *mut leanh::LeanObject,
        17363264175708149920 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4_value
        ) as *mut leanh::LeanObject,
        1678646150249543785 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_4:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5_value
        ) as *mut leanh::LeanObject,
        13924334440726705414 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__6_value
        ) as *mut leanh::LeanObject,
        10870596837306544181 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7_value
        ) as *mut leanh::LeanObject,
        1 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value:
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
        115, 104, 111, 114, 116, 67, 105, 114, 99, 117, 105, 116, 80, 97, 115, 115, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value
        ) as *mut leanh::LeanObject,
        2044961249380779309 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(
    mut v_x_286_: *mut leanh::LeanObject,
    mut v___y_287_: *mut leanh::LeanObject,
    mut v___y_288_: *mut leanh::LeanObject,
    mut v___y_289_: *mut leanh::LeanObject,
    mut v___y_290_: *mut leanh::LeanObject,
    mut v___y_291_: *mut leanh::LeanObject,
    mut v___y_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_288_);
    leanh::lean_inc_ref(v___y_287_);
    v___x_294_ = leanh::lean_apply_7(
        v_x_286_,
        v___y_287_,
        v___y_288_,
        v___y_289_,
        v___y_290_,
        v___y_291_,
        v___y_292_,
        leanh::lean_box(0),
    );
    return v___x_294_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(
    mut v_x_295_: *mut leanh::LeanObject,
    mut v___y_296_: *mut leanh::LeanObject,
    mut v___y_297_: *mut leanh::LeanObject,
    mut v___y_298_: *mut leanh::LeanObject,
    mut v___y_299_: *mut leanh::LeanObject,
    mut v___y_300_: *mut leanh::LeanObject,
    mut v___y_301_: *mut leanh::LeanObject,
    mut v___y_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
    leanh::lean_dec(v___y_297_);
    leanh::lean_dec_ref(v___y_296_);
    return v_res_303_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(
    mut v_mvarId_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
    mut v___y_306_: *mut leanh::LeanObject,
    mut v___y_307_: *mut leanh::LeanObject,
    mut v___y_308_: *mut leanh::LeanObject,
    mut v___y_309_: *mut leanh::LeanObject,
    mut v___y_310_: *mut leanh::LeanObject,
    mut v___y_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_318_: u8 = 0;
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_307_);
                leanh::lean_inc_ref(v___y_306_);
                v___f_313_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_313_, 0, v_x_305_);
                leanh::lean_closure_set(v___f_313_, 1, v___y_306_);
                leanh::lean_closure_set(v___f_313_, 2, v___y_307_);
                v___x_314_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_304_,
                    v___f_313_,
                    v___y_308_,
                    v___y_309_,
                    v___y_310_,
                    v___y_311_,
                );
                if leanh::lean_obj_tag(v___x_314_) == 0 {
                    return v___x_314_;
                } else {
                    v_a_315_ = leanh::lean_ctor_get(v___x_314_, 0);
                    v_isSharedCheck_322_ = (!leanh::lean_is_exclusive(v___x_314_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v___x_317_ = v___x_314_;
                        v_isShared_318_ = v_isSharedCheck_322_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_315_);
                        leanh::lean_dec(v___x_314_);
                        v___x_317_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_321_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
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
    mut v_mvarId_323_: *mut leanh::LeanObject,
    mut v_x_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
    mut v___y_326_: *mut leanh::LeanObject,
    mut v___y_327_: *mut leanh::LeanObject,
    mut v___y_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_323_, v_x_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
    leanh::lean_dec(v___y_330_);
    leanh::lean_dec_ref(v___y_329_);
    leanh::lean_dec(v___y_328_);
    leanh::lean_dec_ref(v___y_327_);
    leanh::lean_dec(v___y_326_);
    leanh::lean_dec_ref(v___y_325_);
    return v_res_332_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(
    mut v_00_u03b1_333_: *mut leanh::LeanObject,
    mut v_mvarId_334_: *mut leanh::LeanObject,
    mut v_x_335_: *mut leanh::LeanObject,
    mut v___y_336_: *mut leanh::LeanObject,
    mut v___y_337_: *mut leanh::LeanObject,
    mut v___y_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
    mut v___y_340_: *mut leanh::LeanObject,
    mut v___y_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_343_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_334_, v_x_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
    return v___x_343_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___boxed(
    mut v_00_u03b1_344_: *mut leanh::LeanObject,
    mut v_mvarId_345_: *mut leanh::LeanObject,
    mut v_x_346_: *mut leanh::LeanObject,
    mut v___y_347_: *mut leanh::LeanObject,
    mut v___y_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
    mut v___y_352_: *mut leanh::LeanObject,
    mut v___y_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(v_00_u03b1_344_, v_mvarId_345_, v_x_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
    leanh::lean_dec(v___y_352_);
    leanh::lean_dec_ref(v___y_351_);
    leanh::lean_dec(v___y_350_);
    leanh::lean_dec_ref(v___y_349_);
    leanh::lean_dec(v___y_348_);
    leanh::lean_dec_ref(v___y_347_);
    return v_res_354_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_356_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__1,
    );
    v___x_358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_358_, 0, v___x_357_);
    return v___x_358_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = leanh::lean_unsigned_to_nat(32);
    v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
    v___x_361_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_361_, 0, v___x_360_);
    return v___x_361_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(
    mut v_theorems_362_: *mut leanh::LeanObject,
    mut v___x_363_: *mut leanh::LeanObject,
    mut v___x_364_: *mut leanh::LeanObject,
    mut v___x_365_: *mut leanh::LeanObject,
    mut v___x_366_: *mut leanh::LeanObject,
    mut v___x_367_: *mut leanh::LeanObject,
    mut v___x_368_: *mut leanh::LeanObject,
    mut v___x_369_: *mut leanh::LeanObject,
    mut v___x_370_: *mut leanh::LeanObject,
    mut v___x_371_: u8,
    mut v___x_372_: u8,
    mut v___x_373_: *mut leanh::LeanObject,
    mut v___x_374_: *mut leanh::LeanObject,
    mut v_goal_375_: *mut leanh::LeanObject,
    mut v___y_376_: *mut leanh::LeanObject,
    mut v___y_377_: *mut leanh::LeanObject,
    mut v___y_378_: *mut leanh::LeanObject,
    mut v___y_379_: *mut leanh::LeanObject,
    mut v___y_380_: *mut leanh::LeanObject,
    mut v___y_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: u8 = 0;
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: usize = 0;
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_417_: u8 = 0;
    let mut v_fst_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_422_: u8 = 0;
    let mut v_snd_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut v_a_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_438_: u8 = 0;
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut v_a_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_446_: u8 = 0;
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_450_: u8 = 0;
    let mut v_a_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_a_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_a_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_a_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v___x_365_);
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
                if leanh::lean_obj_tag(v___x_383_) == 0 {
                    v_a_384_ = leanh::lean_ctor_get(v___x_383_, 0);
                    leanh::lean_inc(v_a_384_);
                    leanh::lean_dec_ref_known(v___x_383_, 1);
                    v___x_385_ =
                        l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__0;
                    v___x_386_ = l_Lean_Name_mkStr6(
                        v___x_366_, v___x_367_, v___x_368_, v___x_369_, v___x_370_, v___x_385_,
                    );
                    leanh::lean_inc(v___x_386_);
                    v___x_387_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                    leanh::lean_ctor_set(v___x_387_, 0, v___x_386_);
                    leanh::lean_ctor_set_uint8(
                        v___x_387_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_371_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_387_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                        v___x_372_,
                    );
                    v___x_388_ = l_Lean_mkConst(v___x_386_, v___x_373_);
                    v___x_389_ = l_Lean_Meta_SimpTheoremsArray_addTheorem(
                        v_a_384_, v___x_387_, v___x_388_, v___x_365_, v___y_378_, v___y_379_,
                        v___y_380_, v___y_381_,
                    );
                    if leanh::lean_obj_tag(v___x_389_) == 0 {
                        v_a_390_ = leanh::lean_ctor_get(v___x_389_, 0);
                        leanh::lean_inc(v_a_390_);
                        leanh::lean_dec_ref_known(v___x_389_, 1);
                        v___x_391_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_381_);
                        if leanh::lean_obj_tag(v___x_391_) == 0 {
                            v_a_392_ = leanh::lean_ctor_get(v___x_391_, 0);
                            leanh::lean_inc(v_a_392_);
                            leanh::lean_dec_ref_known(v___x_391_, 1);
                            v_maxSteps_393_ = leanh::lean_ctor_get(v___y_376_, 1);
                            v___x_394_ = leanh::lean_unsigned_to_nat(2);
                            v___x_395_ = 0;
                            v___x_396_ = leanh::lean_box(0);
                            leanh::lean_inc(v_maxSteps_393_);
                            v___x_397_ = leanh::lean_alloc_ctor(0, 3, (29) as u32);
                            leanh::lean_ctor_set(v___x_397_, 0, v_maxSteps_393_);
                            leanh::lean_ctor_set(v___x_397_, 1, v___x_394_);
                            leanh::lean_ctor_set(v___x_397_, 2, v___x_396_);
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 3)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 4)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 5)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 6)
                                    as u32,
                                v___x_395_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 7)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 9)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 10)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 11)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 12)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 13)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 14)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 15)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 17)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 18)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 19)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 20)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 21)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 22)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 23)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 24)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 25)
                                    as u32,
                                v___x_371_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 26)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 27)
                                    as u32,
                                v___x_372_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_397_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 28)
                                    as u32,
                                v___x_372_,
                            );
                            v___x_398_ = l_Lean_Options_empty;
                            v___x_399_ = l_Lean_Meta_Simp_mkContext___redArg(
                                v___x_397_, v_a_390_, v_a_392_, v___x_398_, v___y_378_, v___y_380_,
                                v___y_381_,
                            );
                            if leanh::lean_obj_tag(v___x_399_) == 0 {
                                v_a_400_ = leanh::lean_ctor_get(v___x_399_, 0);
                                leanh::lean_inc(v_a_400_);
                                leanh::lean_dec_ref_known(v___x_399_, 1);
                                v___x_401_ = l_Lean_Meta_getPropHyps(
                                    v___y_378_, v___y_379_, v___y_380_, v___y_381_,
                                );
                                if leanh::lean_obj_tag(v___x_401_) == 0 {
                                    v_a_402_ = leanh::lean_ctor_get(v___x_401_, 0);
                                    leanh::lean_inc(v_a_402_);
                                    leanh::lean_dec_ref_known(v___x_401_, 1);
                                    v___x_403_ = lean_mk_empty_array_with_capacity(v___x_374_);
                                    v___x_404_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__2);
                                    leanh::lean_inc_n(v___x_374_, 2);
                                    v___x_405_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
                                    leanh::lean_ctor_set(v___x_405_, 1, v___x_374_);
                                    v___x_406_ = leanh::lean_unsigned_to_nat(32);
                                    v___x_407_ = lean_mk_empty_array_with_capacity(v___x_406_);
                                    v___x_408_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___closed__3);
                                    v___x_409_ = 5usize;
                                    v___x_410_ = leanh::lean_alloc_ctor(
                                        0,
                                        4,
                                        (core::mem::size_of::<usize>() * 1) as u32,
                                    );
                                    leanh::lean_ctor_set(v___x_410_, 0, v___x_408_);
                                    leanh::lean_ctor_set(v___x_410_, 1, v___x_407_);
                                    leanh::lean_ctor_set(v___x_410_, 2, v___x_374_);
                                    leanh::lean_ctor_set(v___x_410_, 3, v___x_374_);
                                    leanh::lean_ctor_set_usize(v___x_410_, 4, v___x_409_);
                                    v___x_411_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                    leanh::lean_ctor_set(v___x_411_, 0, v___x_404_);
                                    leanh::lean_ctor_set(v___x_411_, 1, v___x_404_);
                                    leanh::lean_ctor_set(v___x_411_, 2, v___x_404_);
                                    leanh::lean_ctor_set(v___x_411_, 3, v___x_410_);
                                    v___x_412_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_412_, 0, v___x_405_);
                                    leanh::lean_ctor_set(v___x_412_, 1, v___x_411_);
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
                                    if leanh::lean_obj_tag(v___x_413_) == 0 {
                                        v_a_414_ = leanh::lean_ctor_get(v___x_413_, 0);
                                        v_isSharedCheck_434_ =
                                            (!leanh::lean_is_exclusive(v___x_413_)) as u8;
                                        if v_isSharedCheck_434_ == 0 {
                                            v___x_416_ = v___x_413_;
                                            v_isShared_417_ = v_isSharedCheck_434_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_414_);
                                            leanh::lean_dec(v___x_413_);
                                            v___x_416_ = leanh::lean_box(0);
                                            v_isShared_417_ = v_isSharedCheck_434_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v_a_435_ = leanh::lean_ctor_get(v___x_413_, 0);
                                        v_isSharedCheck_442_ =
                                            (!leanh::lean_is_exclusive(v___x_413_)) as u8;
                                        if v_isSharedCheck_442_ == 0 {
                                            v___x_437_ = v___x_413_;
                                            v_isShared_438_ = v_isSharedCheck_442_;
                                            state = 6;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_435_);
                                            leanh::lean_dec(v___x_413_);
                                            v___x_437_ = leanh::lean_box(0);
                                            v_isShared_438_ = v_isSharedCheck_442_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_400_);
                                    leanh::lean_dec(v_goal_375_);
                                    leanh::lean_dec(v___x_374_);
                                    v_a_443_ = leanh::lean_ctor_get(v___x_401_, 0);
                                    v_isSharedCheck_450_ =
                                        (!leanh::lean_is_exclusive(v___x_401_)) as u8;
                                    if v_isSharedCheck_450_ == 0 {
                                        v___x_445_ = v___x_401_;
                                        v_isShared_446_ = v_isSharedCheck_450_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_443_);
                                        leanh::lean_dec(v___x_401_);
                                        v___x_445_ = leanh::lean_box(0);
                                        v_isShared_446_ = v_isSharedCheck_450_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_goal_375_);
                                leanh::lean_dec(v___x_374_);
                                v_a_451_ = leanh::lean_ctor_get(v___x_399_, 0);
                                v_isSharedCheck_458_ =
                                    (!leanh::lean_is_exclusive(v___x_399_)) as u8;
                                if v_isSharedCheck_458_ == 0 {
                                    v___x_453_ = v___x_399_;
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_451_);
                                    leanh::lean_dec(v___x_399_);
                                    v___x_453_ = leanh::lean_box(0);
                                    v_isShared_454_ = v_isSharedCheck_458_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_390_);
                            leanh::lean_dec(v_goal_375_);
                            leanh::lean_dec(v___x_374_);
                            v_a_459_ = leanh::lean_ctor_get(v___x_391_, 0);
                            v_isSharedCheck_466_ =
                                (!leanh::lean_is_exclusive(v___x_391_)) as u8;
                            if v_isSharedCheck_466_ == 0 {
                                v___x_461_ = v___x_391_;
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_459_);
                                leanh::lean_dec(v___x_391_);
                                v___x_461_ = leanh::lean_box(0);
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_goal_375_);
                        leanh::lean_dec(v___x_374_);
                        v_a_467_ = leanh::lean_ctor_get(v___x_389_, 0);
                        v_isSharedCheck_474_ = (!leanh::lean_is_exclusive(v___x_389_)) as u8;
                        if v_isSharedCheck_474_ == 0 {
                            v___x_469_ = v___x_389_;
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_467_);
                            leanh::lean_dec(v___x_389_);
                            v___x_469_ = leanh::lean_box(0);
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_goal_375_);
                    leanh::lean_dec(v___x_374_);
                    leanh::lean_dec(v___x_373_);
                    leanh::lean_dec_ref(v___x_370_);
                    leanh::lean_dec_ref(v___x_369_);
                    leanh::lean_dec_ref(v___x_368_);
                    leanh::lean_dec_ref(v___x_367_);
                    leanh::lean_dec_ref(v___x_366_);
                    leanh::lean_dec_ref(v___x_365_);
                    v_a_475_ = leanh::lean_ctor_get(v___x_383_, 0);
                    v_isSharedCheck_482_ = (!leanh::lean_is_exclusive(v___x_383_)) as u8;
                    if v_isSharedCheck_482_ == 0 {
                        v___x_477_ = v___x_383_;
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_475_);
                        leanh::lean_dec(v___x_383_);
                        v___x_477_ = leanh::lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_418_ = leanh::lean_ctor_get(v_a_414_, 0);
                leanh::lean_inc(v_fst_418_);
                leanh::lean_dec(v_a_414_);
                if leanh::lean_obj_tag(v_fst_418_) == 1 {
                    v_val_419_ = leanh::lean_ctor_get(v_fst_418_, 0);
                    v_isSharedCheck_430_ = (!leanh::lean_is_exclusive(v_fst_418_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_421_ = v_fst_418_;
                        v_isShared_422_ = v_isSharedCheck_430_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_419_);
                        leanh::lean_dec(v_fst_418_);
                        v___x_421_ = leanh::lean_box(0);
                        v_isShared_422_ = v_isSharedCheck_430_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_418_);
                    if v_isShared_417_ == 0 {
                        leanh::lean_ctor_set(v___x_416_, 0, v___x_396_);
                        v___x_432_ = v___x_416_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_396_);
                        v___x_432_ = v_reuseFailAlloc_433_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_423_ = leanh::lean_ctor_get(v_val_419_, 1);
                leanh::lean_inc(v_snd_423_);
                leanh::lean_dec(v_val_419_);
                if v_isShared_422_ == 0 {
                    leanh::lean_ctor_set(v___x_421_, 0, v_snd_423_);
                    v___x_425_ = v___x_421_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_snd_423_);
                    v___x_425_ = v_reuseFailAlloc_429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_417_ == 0 {
                    leanh::lean_ctor_set(v___x_416_, 0, v___x_425_);
                    v___x_427_ = v___x_416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
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
                    v_reuseFailAlloc_441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
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
                    v_reuseFailAlloc_449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
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
                    v_reuseFailAlloc_457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
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
                    v_reuseFailAlloc_465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
                    v_reuseFailAlloc_473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
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
                    v_reuseFailAlloc_481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_theorems_483_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_484_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_485_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_486_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_487_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_488_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_489_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_490_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_491_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_492_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_493_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_494_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_495_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_goal_496_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_497_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_498_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_499_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_500_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_501_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_502_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_503_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___x_5256__boxed_504_: u8 = 0;
    let mut v___x_5257__boxed_505_: u8 = 0;
    let mut v_res_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5256__boxed_504_ = (leanh::lean_unbox(v___x_492_) as u8);
    v___x_5257__boxed_505_ = (leanh::lean_unbox(v___x_493_) as u8);
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
    leanh::lean_dec(v___y_502_);
    leanh::lean_dec_ref(v___y_501_);
    leanh::lean_dec(v___y_500_);
    leanh::lean_dec_ref(v___y_499_);
    leanh::lean_dec(v___y_498_);
    leanh::lean_dec_ref(v___y_497_);
    return v_res_506_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = leanh::lean_box(0);
    v___x_527_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__7;
    v___x_528_ = l_Lean_mkConst(v___x_527_, v___x_526_);
    return v___x_528_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(
    mut v_goal_529_: *mut leanh::LeanObject,
    mut v___y_530_: *mut leanh::LeanObject,
    mut v___y_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
    mut v___y_533_: *mut leanh::LeanObject,
    mut v___y_534_: *mut leanh::LeanObject,
    mut v___y_535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_theorems_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: u8 = 0;
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = leanh::lean_unsigned_to_nat(0);
    v_theorems_538_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__0;
    v___x_539_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__1;
    v___x_540_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__2;
    v___x_541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__3;
    v___x_542_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__4;
    v___x_543_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__5;
    v___x_544_ = 1;
    v___x_545_ = 0;
    v___x_546_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__8;
    v___x_547_ = leanh::lean_box(0);
    v___x_548_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___closed__9,
    );
    v___x_549_ = l_Lean_Meta_simpGlobalConfig;
    v___x_550_ = leanh::lean_box((v___x_544_) as usize);
    v___x_551_ = leanh::lean_box((v___x_545_) as usize);
    leanh::lean_inc(v_goal_529_);
    v___f_552_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed
            as *mut core::ffi::c_void,
        21,
        14,
    );
    leanh::lean_closure_set(v___f_552_, 0, v_theorems_538_);
    leanh::lean_closure_set(v___f_552_, 1, v___x_546_);
    leanh::lean_closure_set(v___f_552_, 2, v___x_548_);
    leanh::lean_closure_set(v___f_552_, 3, v___x_549_);
    leanh::lean_closure_set(v___f_552_, 4, v___x_539_);
    leanh::lean_closure_set(v___f_552_, 5, v___x_540_);
    leanh::lean_closure_set(v___f_552_, 6, v___x_541_);
    leanh::lean_closure_set(v___f_552_, 7, v___x_542_);
    leanh::lean_closure_set(v___f_552_, 8, v___x_543_);
    leanh::lean_closure_set(v___f_552_, 9, v___x_550_);
    leanh::lean_closure_set(v___f_552_, 10, v___x_551_);
    leanh::lean_closure_set(v___f_552_, 11, v___x_547_);
    leanh::lean_closure_set(v___f_552_, 12, v___x_537_);
    leanh::lean_closure_set(v___f_552_, 13, v_goal_529_);
    v___x_553_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_goal_529_, v___f_552_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
    return v___x_553_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed(
    mut v_goal_554_: *mut leanh::LeanObject,
    mut v___y_555_: *mut leanh::LeanObject,
    mut v___y_556_: *mut leanh::LeanObject,
    mut v___y_557_: *mut leanh::LeanObject,
    mut v___y_558_: *mut leanh::LeanObject,
    mut v___y_559_: *mut leanh::LeanObject,
    mut v___y_560_: *mut leanh::LeanObject,
    mut v___y_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(
        v_goal_554_,
        v___y_555_,
        v___y_556_,
        v___y_557_,
        v___y_558_,
        v___y_559_,
        v___y_560_,
    );
    leanh::lean_dec(v___y_560_);
    leanh::lean_dec_ref(v___y_559_);
    leanh::lean_dec(v___y_558_);
    leanh::lean_dec_ref(v___y_557_);
    leanh::lean_dec(v___y_556_);
    leanh::lean_dec_ref(v___y_555_);
    return v_res_562_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
}