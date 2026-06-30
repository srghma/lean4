// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Rewrite
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_push,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::{
    l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt, l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSEvalTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::l_Lean_Meta_SimpExtension_getTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg,
    l_Lean_Meta_Simp_getSEvalSimprocs___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_getPropHyps;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [114, 101, 119, 114, 105, 116, 101, 82, 117, 108, 101, 115, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value
        ) as *mut leanh::LeanObject,
        16396302584987638055 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value:
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
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(
    mut v_x_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
    mut v___y_643_: *mut leanh::LeanObject,
    mut v___y_644_: *mut leanh::LeanObject,
    mut v___y_645_: *mut leanh::LeanObject,
    mut v___y_646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_642_);
    leanh::lean_inc_ref(v___y_641_);
    v___x_648_ = leanh::lean_apply_7(
        v_x_640_,
        v___y_641_,
        v___y_642_,
        v___y_643_,
        v___y_644_,
        v___y_645_,
        v___y_646_,
        leanh::lean_box(0),
    );
    return v___x_648_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0___boxed(
    mut v_x_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
    mut v___y_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
    mut v___y_653_: *mut leanh::LeanObject,
    mut v___y_654_: *mut leanh::LeanObject,
    mut v___y_655_: *mut leanh::LeanObject,
    mut v___y_656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(v_x_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
    leanh::lean_dec(v___y_651_);
    leanh::lean_dec_ref(v___y_650_);
    return v_res_657_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(
    mut v_mvarId_658_: *mut leanh::LeanObject,
    mut v_x_659_: *mut leanh::LeanObject,
    mut v___y_660_: *mut leanh::LeanObject,
    mut v___y_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
    mut v___y_665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_672_: u8 = 0;
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_661_);
                leanh::lean_inc_ref(v___y_660_);
                v___f_667_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_667_, 0, v_x_659_);
                leanh::lean_closure_set(v___f_667_, 1, v___y_660_);
                leanh::lean_closure_set(v___f_667_, 2, v___y_661_);
                v___x_668_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_658_,
                    v___f_667_,
                    v___y_662_,
                    v___y_663_,
                    v___y_664_,
                    v___y_665_,
                );
                if leanh::lean_obj_tag(v___x_668_) == 0 {
                    return v___x_668_;
                } else {
                    v_a_669_ = leanh::lean_ctor_get(v___x_668_, 0);
                    v_isSharedCheck_676_ = (!leanh::lean_is_exclusive(v___x_668_)) as u8;
                    if v_isSharedCheck_676_ == 0 {
                        v___x_671_ = v___x_668_;
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_669_);
                        leanh::lean_dec(v___x_668_);
                        v___x_671_ = leanh::lean_box(0);
                        v_isShared_672_ = v_isSharedCheck_676_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_672_ == 0 {
                    v___x_674_ = v___x_671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_675_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
                    v___x_674_ = v_reuseFailAlloc_675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___boxed(
    mut v_mvarId_677_: *mut leanh::LeanObject,
    mut v_x_678_: *mut leanh::LeanObject,
    mut v___y_679_: *mut leanh::LeanObject,
    mut v___y_680_: *mut leanh::LeanObject,
    mut v___y_681_: *mut leanh::LeanObject,
    mut v___y_682_: *mut leanh::LeanObject,
    mut v___y_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_686_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_mvarId_677_, v_x_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
    leanh::lean_dec(v___y_684_);
    leanh::lean_dec_ref(v___y_683_);
    leanh::lean_dec(v___y_682_);
    leanh::lean_dec_ref(v___y_681_);
    leanh::lean_dec(v___y_680_);
    leanh::lean_dec_ref(v___y_679_);
    return v_res_686_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2(
    mut v_00_u03b1_687_: *mut leanh::LeanObject,
    mut v_mvarId_688_: *mut leanh::LeanObject,
    mut v_x_689_: *mut leanh::LeanObject,
    mut v___y_690_: *mut leanh::LeanObject,
    mut v___y_691_: *mut leanh::LeanObject,
    mut v___y_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
    mut v___y_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_mvarId_688_, v_x_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
    return v___x_697_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___boxed(
    mut v_00_u03b1_698_: *mut leanh::LeanObject,
    mut v_mvarId_699_: *mut leanh::LeanObject,
    mut v_x_700_: *mut leanh::LeanObject,
    mut v___y_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
    mut v___y_705_: *mut leanh::LeanObject,
    mut v___y_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2(v_00_u03b1_698_, v_mvarId_699_, v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
    leanh::lean_dec(v___y_706_);
    leanh::lean_dec_ref(v___y_705_);
    leanh::lean_dec(v___y_704_);
    leanh::lean_dec_ref(v___y_703_);
    leanh::lean_dec(v___y_702_);
    leanh::lean_dec_ref(v___y_701_);
    return v_res_708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(
    mut v_a_709_: *mut leanh::LeanObject,
    mut v_x_710_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_711_: u8 = 0;
    let mut v_key_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_710_) == 0 {
                    v___x_711_ = 0;
                    return v___x_711_;
                } else {
                    v_key_712_ = leanh::lean_ctor_get(v_x_710_, 0);
                    v_tail_713_ = leanh::lean_ctor_get(v_x_710_, 2);
                    v___x_714_ = l_Lean_instBEqFVarId_beq(v_key_712_, v_a_709_);
                    if v___x_714_ == 0 {
                        v_x_710_ = v_tail_713_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_714_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_x_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_718_: u8 = 0;
    let mut v_r_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_716_, v_x_717_);
    leanh::lean_dec(v_x_717_);
    leanh::lean_dec(v_a_716_);
    v_r_719_ = leanh::lean_box((v_res_718_) as usize);
    return v_r_719_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(
    mut v_m_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u64 = 0;
    let mut v___x_725_: u64 = 0;
    let mut v___x_726_: u64 = 0;
    let mut v_fold_727_: u64 = 0;
    let mut v___x_728_: u64 = 0;
    let mut v___x_729_: u64 = 0;
    let mut v___x_730_: u64 = 0;
    let mut v___x_731_: usize = 0;
    let mut v___x_732_: usize = 0;
    let mut v___x_733_: usize = 0;
    let mut v___x_734_: usize = 0;
    let mut v___x_735_: usize = 0;
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    v_buckets_722_ = leanh::lean_ctor_get(v_m_720_, 1);
    v___x_723_ = lean_array_get_size(v_buckets_722_);
    v___x_724_ = l_Lean_instHashableFVarId_hash(v_a_721_);
    v___x_725_ = 32u64;
    v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
    v_fold_727_ = lean_uint64_xor(v___x_724_, v___x_726_);
    v___x_728_ = 16u64;
    v___x_729_ = lean_uint64_shift_right(v_fold_727_, v___x_728_);
    v___x_730_ = lean_uint64_xor(v_fold_727_, v___x_729_);
    v___x_731_ = lean_uint64_to_usize(v___x_730_);
    v___x_732_ = lean_usize_of_nat(v___x_723_);
    v___x_733_ = 1usize;
    v___x_734_ = lean_usize_sub(v___x_732_, v___x_733_);
    v___x_735_ = lean_usize_land(v___x_731_, v___x_734_);
    v___x_736_ = lean_array_uget_borrowed(v_buckets_722_, v___x_735_);
    v___x_737_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_721_, v___x_736_);
    return v___x_737_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg___boxed(
    mut v_m_738_: *mut leanh::LeanObject,
    mut v_a_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_740_: u8 = 0;
    let mut v_r_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_m_738_, v_a_739_);
    leanh::lean_dec(v_a_739_);
    leanh::lean_dec_ref(v_m_738_);
    v_r_741_ = leanh::lean_box((v_res_740_) as usize);
    return v_r_741_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(
    mut v_as_742_: *mut leanh::LeanObject,
    mut v_i_743_: usize,
    mut v_stop_744_: usize,
    mut v_b_745_: *mut leanh::LeanObject,
    mut v___y_746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: usize = 0;
    let mut v___x_751_: usize = 0;
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_753_ = lean_usize_dec_eq(v_i_743_, v_stop_744_);
                if v___x_753_ == 0 {
                    v___x_754_ = lean_st_ref_get(v___y_746_);
                    v_rewriteCache_755_ = leanh::lean_ctor_get(v___x_754_, 0);
                    leanh::lean_inc_ref(v_rewriteCache_755_);
                    leanh::lean_dec(v___x_754_);
                    v___x_756_ = lean_array_uget_borrowed(v_as_742_, v_i_743_);
                    v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_rewriteCache_755_, v___x_756_);
                    leanh::lean_dec_ref(v_rewriteCache_755_);
                    if v___x_757_ == 0 {
                        leanh::lean_inc(v___x_756_);
                        v___x_758_ = lean_array_push(v_b_745_, v___x_756_);
                        v_a_749_ = v___x_758_;
                        state = 1;
                        continue;
                    } else {
                        v_a_749_ = v_b_745_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_759_, 0, v_b_745_);
                    return v___x_759_;
                }
            }
            1 => {
                v___x_750_ = 1usize;
                v___x_751_ = lean_usize_add(v_i_743_, v___x_750_);
                v_i_743_ = v___x_751_;
                v_b_745_ = v_a_749_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg___boxed(
    mut v_as_760_: *mut leanh::LeanObject,
    mut v_i_761_: *mut leanh::LeanObject,
    mut v_stop_762_: *mut leanh::LeanObject,
    mut v_b_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_766_: usize = 0;
    let mut v_stop_boxed_767_: usize = 0;
    let mut v_res_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_766_ = leanh::lean_unbox_usize(v_i_761_);
    leanh::lean_dec(v_i_761_);
    v_stop_boxed_767_ = leanh::lean_unbox_usize(v_stop_762_);
    leanh::lean_dec(v_stop_762_);
    v_res_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_as_760_, v_i_boxed_766_, v_stop_boxed_767_, v_b_763_, v___y_764_);
    leanh::lean_dec(v___y_764_);
    leanh::lean_dec_ref(v_as_760_);
    return v_res_768_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0(
    mut v___y_771_: *mut leanh::LeanObject,
    mut v___y_772_: *mut leanh::LeanObject,
    mut v___y_773_: *mut leanh::LeanObject,
    mut v___y_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: usize = 0;
    let mut v___x_795_: usize = 0;
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: usize = 0;
    let mut v___x_798_: usize = 0;
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_778_ =
                    l_Lean_Meta_getPropHyps(v___y_773_, v___y_774_, v___y_775_, v___y_776_);
                if leanh::lean_obj_tag(v___x_778_) == 0 {
                    v_a_779_ = leanh::lean_ctor_get(v___x_778_, 0);
                    v_isSharedCheck_800_ = (!leanh::lean_is_exclusive(v___x_778_)) as u8;
                    if v_isSharedCheck_800_ == 0 {
                        v___x_781_ = v___x_778_;
                        v_isShared_782_ = v_isSharedCheck_800_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_779_);
                        leanh::lean_dec(v___x_778_);
                        v___x_781_ = leanh::lean_box(0);
                        v_isShared_782_ = v_isSharedCheck_800_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_778_;
                }
            }
            1 => {
                v___x_783_ = leanh::lean_unsigned_to_nat(0);
                v___x_784_ = lean_array_get_size(v_a_779_);
                v___x_785_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0;
                v___x_786_ = lean_nat_dec_lt(v___x_783_, v___x_784_);
                if v___x_786_ == 0 {
                    leanh::lean_dec(v_a_779_);
                    if v_isShared_782_ == 0 {
                        leanh::lean_ctor_set(v___x_781_, 0, v___x_785_);
                        v___x_788_ = v___x_781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_789_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
                        v___x_788_ = v_reuseFailAlloc_789_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_790_ = lean_nat_dec_le(v___x_784_, v___x_784_);
                    if v___x_790_ == 0 {
                        if v___x_786_ == 0 {
                            leanh::lean_dec(v_a_779_);
                            if v_isShared_782_ == 0 {
                                leanh::lean_ctor_set(v___x_781_, 0, v___x_785_);
                                v___x_792_ = v___x_781_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_793_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_785_);
                                v___x_792_ = v_reuseFailAlloc_793_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_781_);
                            v___x_794_ = 0usize;
                            v___x_795_ = lean_usize_of_nat(v___x_784_);
                            v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_a_779_, v___x_794_, v___x_795_, v___x_785_, v___y_772_);
                            leanh::lean_dec(v_a_779_);
                            return v___x_796_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_781_);
                        v___x_797_ = 0usize;
                        v___x_798_ = lean_usize_of_nat(v___x_784_);
                        v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_a_779_, v___x_797_, v___x_798_, v___x_785_, v___y_772_);
                        leanh::lean_dec(v_a_779_);
                        return v___x_799_;
                    }
                }
            }
            2 => {
                return v___x_788_;
            }
            3 => {
                return v___x_792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
    mut v___y_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
    mut v___y_805_: *mut leanh::LeanObject,
    mut v___y_806_: *mut leanh::LeanObject,
    mut v___y_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___lam__0(v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
    leanh::lean_dec(v___y_806_);
    leanh::lean_dec_ref(v___y_805_);
    leanh::lean_dec(v___y_804_);
    leanh::lean_dec_ref(v___y_803_);
    leanh::lean_dec(v___y_802_);
    leanh::lean_dec_ref(v___y_801_);
    return v_res_808_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(
    mut v_goal_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_818_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___closed__0;
    v___x_819_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_goal_810_, v___f_818_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
    return v___x_819_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps___boxed(
    mut v_goal_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
    mut v_a_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(v_goal_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
    leanh::lean_dec(v_a_826_);
    leanh::lean_dec_ref(v_a_825_);
    leanh::lean_dec(v_a_824_);
    leanh::lean_dec_ref(v_a_823_);
    leanh::lean_dec(v_a_822_);
    leanh::lean_dec_ref(v_a_821_);
    return v_res_828_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0(
    mut v_00_u03b2_829_: *mut leanh::LeanObject,
    mut v_m_830_: *mut leanh::LeanObject,
    mut v_a_831_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_832_: u8 = 0;
    v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___redArg(v_m_830_, v_a_831_);
    return v___x_832_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(
    mut v_00_u03b2_833_: *mut leanh::LeanObject,
    mut v_m_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_836_: u8 = 0;
    let mut v_r_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0(v_00_u03b2_833_, v_m_834_, v_a_835_);
    leanh::lean_dec(v_a_835_);
    leanh::lean_dec_ref(v_m_834_);
    v_r_837_ = leanh::lean_box((v_res_836_) as usize);
    return v_r_837_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1(
    mut v_as_838_: *mut leanh::LeanObject,
    mut v_i_839_: usize,
    mut v_stop_840_: usize,
    mut v_b_841_: *mut leanh::LeanObject,
    mut v___y_842_: *mut leanh::LeanObject,
    mut v___y_843_: *mut leanh::LeanObject,
    mut v___y_844_: *mut leanh::LeanObject,
    mut v___y_845_: *mut leanh::LeanObject,
    mut v___y_846_: *mut leanh::LeanObject,
    mut v___y_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___redArg(v_as_838_, v_i_839_, v_stop_840_, v_b_841_, v___y_843_);
    return v___x_849_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1___boxed(
    mut v_as_850_: *mut leanh::LeanObject,
    mut v_i_851_: *mut leanh::LeanObject,
    mut v_stop_852_: *mut leanh::LeanObject,
    mut v_b_853_: *mut leanh::LeanObject,
    mut v___y_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
    mut v___y_856_: *mut leanh::LeanObject,
    mut v___y_857_: *mut leanh::LeanObject,
    mut v___y_858_: *mut leanh::LeanObject,
    mut v___y_859_: *mut leanh::LeanObject,
    mut v___y_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_861_: usize = 0;
    let mut v_stop_boxed_862_: usize = 0;
    let mut v_res_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_861_ = leanh::lean_unbox_usize(v_i_851_);
    leanh::lean_dec(v_i_851_);
    v_stop_boxed_862_ = leanh::lean_unbox_usize(v_stop_852_);
    leanh::lean_dec(v_stop_852_);
    v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__1(v_as_850_, v_i_boxed_861_, v_stop_boxed_862_, v_b_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
    leanh::lean_dec(v___y_859_);
    leanh::lean_dec_ref(v___y_858_);
    leanh::lean_dec(v___y_857_);
    leanh::lean_dec_ref(v___y_856_);
    leanh::lean_dec(v___y_855_);
    leanh::lean_dec_ref(v___y_854_);
    leanh::lean_dec_ref(v_as_850_);
    return v_res_863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(
    mut v_00_u03b2_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
    mut v_x_866_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_867_: u8 = 0;
    v___x_867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_865_, v_x_866_);
    return v___x_867_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(
    mut v_00_u03b2_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_x_870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_871_: u8 = 0;
    let mut v_r_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(v_00_u03b2_868_, v_a_869_, v_x_870_);
    leanh::lean_dec(v_x_870_);
    leanh::lean_dec(v_a_869_);
    v_r_872_ = leanh::lean_box((v_res_871_) as usize);
    return v_r_872_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_873_: *mut leanh::LeanObject,
    mut v_x_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_880_: u8 = 0;
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: u64 = 0;
    let mut v___x_883_: u64 = 0;
    let mut v___x_884_: u64 = 0;
    let mut v_fold_885_: u64 = 0;
    let mut v___x_886_: u64 = 0;
    let mut v___x_887_: u64 = 0;
    let mut v___x_888_: u64 = 0;
    let mut v___x_889_: usize = 0;
    let mut v___x_890_: usize = 0;
    let mut v___x_891_: usize = 0;
    let mut v___x_892_: usize = 0;
    let mut v___x_893_: usize = 0;
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_874_) == 0 {
                    return v_x_873_;
                } else {
                    v_key_875_ = leanh::lean_ctor_get(v_x_874_, 0);
                    v_value_876_ = leanh::lean_ctor_get(v_x_874_, 1);
                    v_tail_877_ = leanh::lean_ctor_get(v_x_874_, 2);
                    v_isSharedCheck_900_ = (!leanh::lean_is_exclusive(v_x_874_)) as u8;
                    if v_isSharedCheck_900_ == 0 {
                        v___x_879_ = v_x_874_;
                        v_isShared_880_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_877_);
                        leanh::lean_inc(v_value_876_);
                        leanh::lean_inc(v_key_875_);
                        leanh::lean_dec(v_x_874_);
                        v___x_879_ = leanh::lean_box(0);
                        v_isShared_880_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_881_ = lean_array_get_size(v_x_873_);
                v___x_882_ = l_Lean_instHashableFVarId_hash(v_key_875_);
                v___x_883_ = 32u64;
                v___x_884_ = lean_uint64_shift_right(v___x_882_, v___x_883_);
                v_fold_885_ = lean_uint64_xor(v___x_882_, v___x_884_);
                v___x_886_ = 16u64;
                v___x_887_ = lean_uint64_shift_right(v_fold_885_, v___x_886_);
                v___x_888_ = lean_uint64_xor(v_fold_885_, v___x_887_);
                v___x_889_ = lean_uint64_to_usize(v___x_888_);
                v___x_890_ = lean_usize_of_nat(v___x_881_);
                v___x_891_ = 1usize;
                v___x_892_ = lean_usize_sub(v___x_890_, v___x_891_);
                v___x_893_ = lean_usize_land(v___x_889_, v___x_892_);
                v___x_894_ = lean_array_uget_borrowed(v_x_873_, v___x_893_);
                leanh::lean_inc(v___x_894_);
                if v_isShared_880_ == 0 {
                    leanh::lean_ctor_set(v___x_879_, 2, v___x_894_);
                    v___x_896_ = v___x_879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_key_875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_899_, 1, v_value_876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_894_);
                    v___x_896_ = v_reuseFailAlloc_899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_897_ = lean_array_uset(v_x_873_, v___x_893_, v___x_896_);
                v_x_873_ = v___x_897_;
                v_x_874_ = v_tail_877_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(
    mut v_i_901_: *mut leanh::LeanObject,
    mut v_source_902_: *mut leanh::LeanObject,
    mut v_target_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    let mut v_es_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_904_ = lean_array_get_size(v_source_902_);
                v___x_905_ = lean_nat_dec_lt(v_i_901_, v___x_904_);
                if v___x_905_ == 0 {
                    leanh::lean_dec_ref(v_source_902_);
                    leanh::lean_dec(v_i_901_);
                    return v_target_903_;
                } else {
                    v_es_906_ = lean_array_fget(v_source_902_, v_i_901_);
                    v___x_907_ = leanh::lean_box(0);
                    v_source_908_ = lean_array_fset(v_source_902_, v_i_901_, v___x_907_);
                    v_target_909_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(v_target_903_, v_es_906_);
                    v___x_910_ = leanh::lean_unsigned_to_nat(1);
                    v___x_911_ = lean_nat_add(v_i_901_, v___x_910_);
                    leanh::lean_dec(v_i_901_);
                    v_i_901_ = v___x_911_;
                    v_source_902_ = v_source_908_;
                    v_target_903_ = v_target_909_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(
    mut v_data_913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_array_get_size(v_data_913_);
    v___x_915_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_916_ = lean_nat_mul(v___x_914_, v___x_915_);
    v___x_917_ = leanh::lean_unsigned_to_nat(0);
    v___x_918_ = leanh::lean_box(0);
    v___x_919_ = lean_mk_array(v_nbuckets_916_, v___x_918_);
    v___x_920_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(v___x_917_, v_data_913_, v___x_919_);
    return v___x_920_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(
    mut v_m_921_: *mut leanh::LeanObject,
    mut v_a_922_: *mut leanh::LeanObject,
    mut v_b_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: u64 = 0;
    let mut v___x_928_: u64 = 0;
    let mut v___x_929_: u64 = 0;
    let mut v_fold_930_: u64 = 0;
    let mut v___x_931_: u64 = 0;
    let mut v___x_932_: u64 = 0;
    let mut v___x_933_: u64 = 0;
    let mut v___x_934_: usize = 0;
    let mut v___x_935_: usize = 0;
    let mut v___x_936_: usize = 0;
    let mut v___x_937_: usize = 0;
    let mut v___x_938_: usize = 0;
    let mut v_bkt_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: u8 = 0;
    let mut v_val_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut v_unused_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_924_ = leanh::lean_ctor_get(v_m_921_, 0);
                v_buckets_925_ = leanh::lean_ctor_get(v_m_921_, 1);
                v___x_926_ = lean_array_get_size(v_buckets_925_);
                v___x_927_ = l_Lean_instHashableFVarId_hash(v_a_922_);
                v___x_928_ = 32u64;
                v___x_929_ = lean_uint64_shift_right(v___x_927_, v___x_928_);
                v_fold_930_ = lean_uint64_xor(v___x_927_, v___x_929_);
                v___x_931_ = 16u64;
                v___x_932_ = lean_uint64_shift_right(v_fold_930_, v___x_931_);
                v___x_933_ = lean_uint64_xor(v_fold_930_, v___x_932_);
                v___x_934_ = lean_uint64_to_usize(v___x_933_);
                v___x_935_ = lean_usize_of_nat(v___x_926_);
                v___x_936_ = 1usize;
                v___x_937_ = lean_usize_sub(v___x_935_, v___x_936_);
                v___x_938_ = lean_usize_land(v___x_934_, v___x_937_);
                v_bkt_939_ = lean_array_uget_borrowed(v_buckets_925_, v___x_938_);
                v___x_940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(v_a_922_, v_bkt_939_);
                if v___x_940_ == 0 {
                    leanh::lean_inc_ref(v_buckets_925_);
                    leanh::lean_inc(v_size_924_);
                    v_isSharedCheck_961_ = (!leanh::lean_is_exclusive(v_m_921_)) as u8;
                    if v_isSharedCheck_961_ == 0 {
                        v_unused_962_ = leanh::lean_ctor_get(v_m_921_, 1);
                        leanh::lean_dec(v_unused_962_);
                        v_unused_963_ = leanh::lean_ctor_get(v_m_921_, 0);
                        leanh::lean_dec(v_unused_963_);
                        v___x_942_ = v_m_921_;
                        v_isShared_943_ = v_isSharedCheck_961_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_921_);
                        v___x_942_ = leanh::lean_box(0);
                        v_isShared_943_ = v_isSharedCheck_961_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_923_);
                    leanh::lean_dec(v_a_922_);
                    return v_m_921_;
                }
            }
            1 => {
                v___x_944_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_945_ = lean_nat_add(v_size_924_, v___x_944_);
                leanh::lean_dec(v_size_924_);
                leanh::lean_inc(v_bkt_939_);
                v___x_946_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_946_, 0, v_a_922_);
                leanh::lean_ctor_set(v___x_946_, 1, v_b_923_);
                leanh::lean_ctor_set(v___x_946_, 2, v_bkt_939_);
                v_buckets_x27_947_ = lean_array_uset(v_buckets_925_, v___x_938_, v___x_946_);
                v___x_948_ = leanh::lean_unsigned_to_nat(4);
                v___x_949_ = lean_nat_mul(v_size_x27_945_, v___x_948_);
                v___x_950_ = leanh::lean_unsigned_to_nat(3);
                v___x_951_ = lean_nat_div(v___x_949_, v___x_950_);
                leanh::lean_dec(v___x_949_);
                v___x_952_ = lean_array_get_size(v_buckets_x27_947_);
                v___x_953_ = lean_nat_dec_le(v___x_951_, v___x_952_);
                leanh::lean_dec(v___x_951_);
                if v___x_953_ == 0 {
                    v_val_954_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(v_buckets_x27_947_);
                    if v_isShared_943_ == 0 {
                        leanh::lean_ctor_set(v___x_942_, 1, v_val_954_);
                        leanh::lean_ctor_set(v___x_942_, 0, v_size_x27_945_);
                        v___x_956_ = v___x_942_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_957_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_957_, 0, v_size_x27_945_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_957_, 1, v_val_954_);
                        v___x_956_ = v_reuseFailAlloc_957_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_943_ == 0 {
                        leanh::lean_ctor_set(v___x_942_, 1, v_buckets_x27_947_);
                        leanh::lean_ctor_set(v___x_942_, 0, v_size_x27_945_);
                        v___x_959_ = v___x_942_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_960_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_960_, 0, v_size_x27_945_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_960_, 1, v_buckets_x27_947_);
                        v___x_959_ = v_reuseFailAlloc_960_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_956_;
            }
            3 => {
                return v___x_959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(
    mut v_as_964_: *mut leanh::LeanObject,
    mut v_i_965_: usize,
    mut v_stop_966_: usize,
    mut v_b_967_: *mut leanh::LeanObject,
    mut v___y_968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_970_: u8 = 0;
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rewriteCache_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acNfCache_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeAnalysis_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: usize = 0;
    let mut v___x_985_: usize = 0;
    let mut v_reuseFailAlloc_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_988_: u8 = 0;
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_970_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
                if v___x_970_ == 0 {
                    v___x_971_ = lean_st_ref_take(v___y_968_);
                    v_rewriteCache_972_ = leanh::lean_ctor_get(v___x_971_, 0);
                    v_acNfCache_973_ = leanh::lean_ctor_get(v___x_971_, 1);
                    v_typeAnalysis_974_ = leanh::lean_ctor_get(v___x_971_, 2);
                    v_isSharedCheck_988_ = (!leanh::lean_is_exclusive(v___x_971_)) as u8;
                    if v_isSharedCheck_988_ == 0 {
                        v___x_976_ = v___x_971_;
                        v_isShared_977_ = v_isSharedCheck_988_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_typeAnalysis_974_);
                        leanh::lean_inc(v_acNfCache_973_);
                        leanh::lean_inc(v_rewriteCache_972_);
                        leanh::lean_dec(v___x_971_);
                        v___x_976_ = leanh::lean_box(0);
                        v_isShared_977_ = v_isSharedCheck_988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_989_, 0, v_b_967_);
                    return v___x_989_;
                }
            }
            1 => {
                v___x_978_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
                v___x_979_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_978_);
                v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_rewriteCache_972_, v___x_978_, v___x_979_);
                if v_isShared_977_ == 0 {
                    leanh::lean_ctor_set(v___x_976_, 0, v___x_980_);
                    v___x_982_ = v___x_976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_987_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_987_, 1, v_acNfCache_973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_987_, 2, v_typeAnalysis_974_);
                    v___x_982_ = v_reuseFailAlloc_987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_983_ = lean_st_ref_set(v___y_968_, v___x_982_);
                v___x_984_ = 1usize;
                v___x_985_ = lean_usize_add(v_i_965_, v___x_984_);
                v_i_965_ = v___x_985_;
                v_b_967_ = v___x_979_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(
    mut v_as_990_: *mut leanh::LeanObject,
    mut v_i_991_: *mut leanh::LeanObject,
    mut v_stop_992_: *mut leanh::LeanObject,
    mut v_b_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_996_: usize = 0;
    let mut v_stop_boxed_997_: usize = 0;
    let mut v_res_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_996_ = leanh::lean_unbox_usize(v_i_991_);
    leanh::lean_dec(v_i_991_);
    v_stop_boxed_997_ = leanh::lean_unbox_usize(v_stop_992_);
    leanh::lean_dec(v_stop_992_);
    v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_as_990_, v_i_boxed_996_, v_stop_boxed_997_, v_b_993_, v___y_994_);
    leanh::lean_dec(v___y_994_);
    leanh::lean_dec_ref(v_as_990_);
    return v_res_998_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(
    mut v___x_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1011_: u8 = 0;
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: u8 = 0;
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: usize = 0;
    let mut v___x_1023_: usize = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: usize = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1028_: u8 = 0;
    let mut v_a_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1032_: u8 = 0;
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1007_ =
                    l_Lean_Meta_getPropHyps(v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
                if leanh::lean_obj_tag(v___x_1007_) == 0 {
                    v_a_1008_ = leanh::lean_ctor_get(v___x_1007_, 0);
                    v_isSharedCheck_1028_ = (!leanh::lean_is_exclusive(v___x_1007_)) as u8;
                    if v_isSharedCheck_1028_ == 0 {
                        v___x_1010_ = v___x_1007_;
                        v_isShared_1011_ = v_isSharedCheck_1028_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1008_);
                        leanh::lean_dec(v___x_1007_);
                        v___x_1010_ = leanh::lean_box(0);
                        v_isShared_1011_ = v_isSharedCheck_1028_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1029_ = leanh::lean_ctor_get(v___x_1007_, 0);
                    v_isSharedCheck_1036_ = (!leanh::lean_is_exclusive(v___x_1007_)) as u8;
                    if v_isSharedCheck_1036_ == 0 {
                        v___x_1031_ = v___x_1007_;
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1029_);
                        leanh::lean_dec(v___x_1007_);
                        v___x_1031_ = leanh::lean_box(0);
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1012_ = lean_array_get_size(v_a_1008_);
                v___x_1013_ = leanh::lean_box(0);
                v___x_1014_ = lean_nat_dec_lt(v___x_999_, v___x_1012_);
                if v___x_1014_ == 0 {
                    leanh::lean_dec(v_a_1008_);
                    if v_isShared_1011_ == 0 {
                        leanh::lean_ctor_set(v___x_1010_, 0, v___x_1013_);
                        v___x_1016_ = v___x_1010_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
                        v___x_1016_ = v_reuseFailAlloc_1017_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1018_ = lean_nat_dec_le(v___x_1012_, v___x_1012_);
                    if v___x_1018_ == 0 {
                        if v___x_1014_ == 0 {
                            leanh::lean_dec(v_a_1008_);
                            if v_isShared_1011_ == 0 {
                                leanh::lean_ctor_set(v___x_1010_, 0, v___x_1013_);
                                v___x_1020_ = v___x_1010_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1021_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1013_);
                                v___x_1020_ = v_reuseFailAlloc_1021_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1010_);
                            v___x_1022_ = 0usize;
                            v___x_1023_ = lean_usize_of_nat(v___x_1012_);
                            v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_a_1008_, v___x_1022_, v___x_1023_, v___x_1013_, v___y_1001_);
                            leanh::lean_dec(v_a_1008_);
                            return v___x_1024_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1010_);
                        v___x_1025_ = 0usize;
                        v___x_1026_ = lean_usize_of_nat(v___x_1012_);
                        v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_a_1008_, v___x_1025_, v___x_1026_, v___x_1013_, v___y_1001_);
                        leanh::lean_dec(v_a_1008_);
                        return v___x_1027_;
                    }
                }
            }
            2 => {
                return v___x_1016_;
            }
            3 => {
                return v___x_1020_;
            }
            4 => {
                if v_isShared_1032_ == 0 {
                    v___x_1034_ = v___x_1031_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(
    mut v___x_1037_: *mut leanh::LeanObject,
    mut v___y_1038_: *mut leanh::LeanObject,
    mut v___y_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
    mut v___y_1041_: *mut leanh::LeanObject,
    mut v___y_1042_: *mut leanh::LeanObject,
    mut v___y_1043_: *mut leanh::LeanObject,
    mut v___y_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(
        v___x_1037_,
        v___y_1038_,
        v___y_1039_,
        v___y_1040_,
        v___y_1041_,
        v___y_1042_,
        v___y_1043_,
    );
    leanh::lean_dec(v___y_1043_);
    leanh::lean_dec_ref(v___y_1042_);
    leanh::lean_dec(v___y_1041_);
    leanh::lean_dec_ref(v___y_1040_);
    leanh::lean_dec(v___y_1039_);
    leanh::lean_dec_ref(v___y_1038_);
    leanh::lean_dec(v___x_1037_);
    return v_res_1045_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1046_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__0,
    );
    v___x_1048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1048_, 0, v___x_1047_);
    return v___x_1048_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = leanh::lean_unsigned_to_nat(0);
    v___x_1050_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1,
    );
    v___x_1051_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1051_, 0, v___x_1050_);
    leanh::lean_ctor_set(v___x_1051_, 1, v___x_1049_);
    return v___x_1051_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = leanh::lean_unsigned_to_nat(32);
    v___x_1053_ = lean_mk_empty_array_with_capacity(v___x_1052_);
    v___x_1054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1054_, 0, v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = 5usize;
    v___x_1056_ = leanh::lean_unsigned_to_nat(0);
    v___x_1057_ = leanh::lean_unsigned_to_nat(32);
    v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_1057_);
    v___x_1059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__3,
    );
    v___x_1060_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1060_, 0, v___x_1059_);
    leanh::lean_ctor_set(v___x_1060_, 1, v___x_1058_);
    leanh::lean_ctor_set(v___x_1060_, 2, v___x_1056_);
    leanh::lean_ctor_set(v___x_1060_, 3, v___x_1056_);
    leanh::lean_ctor_set_usize(v___x_1060_, 4, v___x_1055_);
    return v___x_1060_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__4,
    );
    v___x_1062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__1,
    );
    v___x_1063_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1063_, 0, v___x_1062_);
    leanh::lean_ctor_set(v___x_1063_, 1, v___x_1062_);
    leanh::lean_ctor_set(v___x_1063_, 2, v___x_1062_);
    leanh::lean_ctor_set(v___x_1063_, 3, v___x_1061_);
    return v___x_1063_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__5,
    );
    v___x_1065_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__2,
    );
    v___x_1066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1066_, 0, v___x_1065_);
    leanh::lean_ctor_set(v___x_1066_, 1, v___x_1064_);
    return v___x_1066_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(
    mut v_goal_1069_: *mut leanh::LeanObject,
    mut v___y_1070_: *mut leanh::LeanObject,
    mut v___y_1071_: *mut leanh::LeanObject,
    mut v___y_1072_: *mut leanh::LeanObject,
    mut v___y_1073_: *mut leanh::LeanObject,
    mut v___y_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: u8 = 0;
    let mut v___x_1092_: u8 = 0;
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v_fst_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1122_: u8 = 0;
    let mut v_snd_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1135_: u8 = 0;
    let mut v_unused_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1144_: u8 = 0;
    let mut v_isSharedCheck_1145_: u8 = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1149_: u8 = 0;
    let mut v_a_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1162_: u8 = 0;
    let mut v_a_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v_a_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1174_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_a_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut v_a_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_a_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1202_: u8 = 0;
    let mut v_a_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_a_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1077_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
                v___x_1078_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_1077_, v___y_1075_);
                if leanh::lean_obj_tag(v___x_1078_) == 0 {
                    v_a_1079_ = leanh::lean_ctor_get(v___x_1078_, 0);
                    leanh::lean_inc(v_a_1079_);
                    leanh::lean_dec_ref_known(v___x_1078_, 1);
                    v___x_1080_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeSimprocExt;
                    v___x_1081_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(
                        v___x_1080_,
                        v___y_1075_,
                    );
                    if leanh::lean_obj_tag(v___x_1081_) == 0 {
                        v_a_1082_ = leanh::lean_ctor_get(v___x_1081_, 0);
                        leanh::lean_inc(v_a_1082_);
                        leanh::lean_dec_ref_known(v___x_1081_, 1);
                        v___x_1083_ = l_Lean_Meta_getSEvalTheorems___redArg(v___y_1075_);
                        if leanh::lean_obj_tag(v___x_1083_) == 0 {
                            v_a_1084_ = leanh::lean_ctor_get(v___x_1083_, 0);
                            leanh::lean_inc(v_a_1084_);
                            leanh::lean_dec_ref_known(v___x_1083_, 1);
                            v___x_1085_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v___y_1075_);
                            if leanh::lean_obj_tag(v___x_1085_) == 0 {
                                v_a_1086_ = leanh::lean_ctor_get(v___x_1085_, 0);
                                leanh::lean_inc(v_a_1086_);
                                leanh::lean_dec_ref_known(v___x_1085_, 1);
                                v___x_1087_ =
                                    l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_1075_);
                                if leanh::lean_obj_tag(v___x_1087_) == 0 {
                                    v_a_1088_ = leanh::lean_ctor_get(v___x_1087_, 0);
                                    leanh::lean_inc(v_a_1088_);
                                    leanh::lean_dec_ref_known(v___x_1087_, 1);
                                    v_maxSteps_1089_ = leanh::lean_ctor_get(v___y_1070_, 1);
                                    v___x_1090_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_1091_ = 0;
                                    v___x_1092_ = 1;
                                    v___x_1093_ = 0;
                                    v___x_1094_ = leanh::lean_box(0);
                                    leanh::lean_inc(v_maxSteps_1089_);
                                    v___x_1095_ = leanh::lean_alloc_ctor(0, 3, (29) as u32);
                                    leanh::lean_ctor_set(v___x_1095_, 0, v_maxSteps_1089_);
                                    leanh::lean_ctor_set(v___x_1095_, 1, v___x_1090_);
                                    leanh::lean_ctor_set(v___x_1095_, 2, v___x_1094_);
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                                            as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 1) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 2) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 3) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 4) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 5) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 6) as u32,
                                        v___x_1093_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 7) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 8) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 9) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 10) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 11) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 12) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 13) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 14) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 15) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 16) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 17) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 18) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 19) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 20) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 21) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 22) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 23) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 24) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 25) as u32,
                                        v___x_1092_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 26) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 27) as u32,
                                        v___x_1091_,
                                    );
                                    leanh::lean_ctor_set_uint8(
                                        v___x_1095_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 28) as u32,
                                        v___x_1092_,
                                    );
                                    v___x_1096_ = lean_mk_empty_array_with_capacity(v___x_1090_);
                                    leanh::lean_inc_ref(v___x_1096_);
                                    v___x_1097_ = lean_array_push(v___x_1096_, v_a_1079_);
                                    v___x_1098_ = lean_array_push(v___x_1097_, v_a_1084_);
                                    v___x_1099_ = l_Lean_Options_empty;
                                    v___x_1100_ = l_Lean_Meta_Simp_mkContext___redArg(
                                        v___x_1095_,
                                        v___x_1098_,
                                        v_a_1088_,
                                        v___x_1099_,
                                        v___y_1072_,
                                        v___y_1074_,
                                        v___y_1075_,
                                    );
                                    if leanh::lean_obj_tag(v___x_1100_) == 0 {
                                        v_a_1101_ = leanh::lean_ctor_get(v___x_1100_, 0);
                                        leanh::lean_inc(v_a_1101_);
                                        leanh::lean_dec_ref_known(v___x_1100_, 1);
                                        leanh::lean_inc(v_goal_1069_);
                                        v___x_1102_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps(v_goal_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
                                        if leanh::lean_obj_tag(v___x_1102_) == 0 {
                                            v_a_1103_ = leanh::lean_ctor_get(v___x_1102_, 0);
                                            v_isSharedCheck_1162_ =
                                                (!leanh::lean_is_exclusive(v___x_1102_))
                                                    as u8;
                                            if v_isSharedCheck_1162_ == 0 {
                                                v___x_1105_ = v___x_1102_;
                                                v_isShared_1106_ = v_isSharedCheck_1162_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1103_);
                                                leanh::lean_dec(v___x_1102_);
                                                v___x_1105_ = leanh::lean_box(0);
                                                v_isShared_1106_ = v_isSharedCheck_1162_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_1101_);
                                            leanh::lean_dec_ref(v___x_1096_);
                                            leanh::lean_dec(v_a_1086_);
                                            leanh::lean_dec(v_a_1082_);
                                            leanh::lean_dec(v_goal_1069_);
                                            v_a_1163_ = leanh::lean_ctor_get(v___x_1102_, 0);
                                            v_isSharedCheck_1170_ =
                                                (!leanh::lean_is_exclusive(v___x_1102_))
                                                    as u8;
                                            if v_isSharedCheck_1170_ == 0 {
                                                v___x_1165_ = v___x_1102_;
                                                v_isShared_1166_ = v_isSharedCheck_1170_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1163_);
                                                leanh::lean_dec(v___x_1102_);
                                                v___x_1165_ = leanh::lean_box(0);
                                                v_isShared_1166_ = v_isSharedCheck_1170_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_1096_);
                                        leanh::lean_dec(v_a_1086_);
                                        leanh::lean_dec(v_a_1082_);
                                        leanh::lean_dec(v_goal_1069_);
                                        v_a_1171_ = leanh::lean_ctor_get(v___x_1100_, 0);
                                        v_isSharedCheck_1178_ =
                                            (!leanh::lean_is_exclusive(v___x_1100_)) as u8;
                                        if v_isSharedCheck_1178_ == 0 {
                                            v___x_1173_ = v___x_1100_;
                                            v_isShared_1174_ = v_isSharedCheck_1178_;
                                            state = 15;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1171_);
                                            leanh::lean_dec(v___x_1100_);
                                            v___x_1173_ = leanh::lean_box(0);
                                            v_isShared_1174_ = v_isSharedCheck_1178_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1086_);
                                    leanh::lean_dec(v_a_1084_);
                                    leanh::lean_dec(v_a_1082_);
                                    leanh::lean_dec(v_a_1079_);
                                    leanh::lean_dec(v_goal_1069_);
                                    v_a_1179_ = leanh::lean_ctor_get(v___x_1087_, 0);
                                    v_isSharedCheck_1186_ =
                                        (!leanh::lean_is_exclusive(v___x_1087_)) as u8;
                                    if v_isSharedCheck_1186_ == 0 {
                                        v___x_1181_ = v___x_1087_;
                                        v_isShared_1182_ = v_isSharedCheck_1186_;
                                        state = 17;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1179_);
                                        leanh::lean_dec(v___x_1087_);
                                        v___x_1181_ = leanh::lean_box(0);
                                        v_isShared_1182_ = v_isSharedCheck_1186_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_1084_);
                                leanh::lean_dec(v_a_1082_);
                                leanh::lean_dec(v_a_1079_);
                                leanh::lean_dec(v_goal_1069_);
                                v_a_1187_ = leanh::lean_ctor_get(v___x_1085_, 0);
                                v_isSharedCheck_1194_ =
                                    (!leanh::lean_is_exclusive(v___x_1085_)) as u8;
                                if v_isSharedCheck_1194_ == 0 {
                                    v___x_1189_ = v___x_1085_;
                                    v_isShared_1190_ = v_isSharedCheck_1194_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1187_);
                                    leanh::lean_dec(v___x_1085_);
                                    v___x_1189_ = leanh::lean_box(0);
                                    v_isShared_1190_ = v_isSharedCheck_1194_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_1082_);
                            leanh::lean_dec(v_a_1079_);
                            leanh::lean_dec(v_goal_1069_);
                            v_a_1195_ = leanh::lean_ctor_get(v___x_1083_, 0);
                            v_isSharedCheck_1202_ =
                                (!leanh::lean_is_exclusive(v___x_1083_)) as u8;
                            if v_isSharedCheck_1202_ == 0 {
                                v___x_1197_ = v___x_1083_;
                                v_isShared_1198_ = v_isSharedCheck_1202_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1195_);
                                leanh::lean_dec(v___x_1083_);
                                v___x_1197_ = leanh::lean_box(0);
                                v_isShared_1198_ = v_isSharedCheck_1202_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1079_);
                        leanh::lean_dec(v_goal_1069_);
                        v_a_1203_ = leanh::lean_ctor_get(v___x_1081_, 0);
                        v_isSharedCheck_1210_ =
                            (!leanh::lean_is_exclusive(v___x_1081_)) as u8;
                        if v_isSharedCheck_1210_ == 0 {
                            v___x_1205_ = v___x_1081_;
                            v_isShared_1206_ = v_isSharedCheck_1210_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1203_);
                            leanh::lean_dec(v___x_1081_);
                            v___x_1205_ = leanh::lean_box(0);
                            v_isShared_1206_ = v_isSharedCheck_1210_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_goal_1069_);
                    v_a_1211_ = leanh::lean_ctor_get(v___x_1078_, 0);
                    v_isSharedCheck_1218_ = (!leanh::lean_is_exclusive(v___x_1078_)) as u8;
                    if v_isSharedCheck_1218_ == 0 {
                        v___x_1213_ = v___x_1078_;
                        v_isShared_1214_ = v_isSharedCheck_1218_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1211_);
                        leanh::lean_dec(v___x_1078_);
                        v___x_1213_ = leanh::lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1218_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1107_ = lean_array_get_size(v_a_1103_);
                v___x_1108_ = leanh::lean_unsigned_to_nat(0);
                v___x_1109_ = lean_nat_dec_eq(v___x_1107_, v___x_1108_);
                if v___x_1109_ == 0 {
                    leanh::lean_del_object(v___x_1105_);
                    v___x_1110_ = lean_array_push(v___x_1096_, v_a_1082_);
                    v___x_1111_ = lean_array_push(v___x_1110_, v_a_1086_);
                    v___x_1112_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__6);
                    v___x_1113_ = l_Lean_Meta_simpGoal(
                        v_goal_1069_,
                        v_a_1101_,
                        v___x_1111_,
                        v___x_1094_,
                        v___x_1092_,
                        v_a_1103_,
                        v___x_1112_,
                        v___y_1072_,
                        v___y_1073_,
                        v___y_1074_,
                        v___y_1075_,
                    );
                    if leanh::lean_obj_tag(v___x_1113_) == 0 {
                        v_a_1114_ = leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1149_ =
                            (!leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1149_ == 0 {
                            v___x_1116_ = v___x_1113_;
                            v_isShared_1117_ = v_isSharedCheck_1149_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1114_);
                            leanh::lean_dec(v___x_1113_);
                            v___x_1116_ = leanh::lean_box(0);
                            v_isShared_1117_ = v_isSharedCheck_1149_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1150_ = leanh::lean_ctor_get(v___x_1113_, 0);
                        v_isSharedCheck_1157_ =
                            (!leanh::lean_is_exclusive(v___x_1113_)) as u8;
                        if v_isSharedCheck_1157_ == 0 {
                            v___x_1152_ = v___x_1113_;
                            v_isShared_1153_ = v_isSharedCheck_1157_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1150_);
                            leanh::lean_dec(v___x_1113_);
                            v___x_1152_ = leanh::lean_box(0);
                            v_isShared_1153_ = v_isSharedCheck_1157_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1103_);
                    leanh::lean_dec(v_a_1101_);
                    leanh::lean_dec_ref(v___x_1096_);
                    leanh::lean_dec(v_a_1086_);
                    leanh::lean_dec(v_a_1082_);
                    v___x_1158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1158_, 0, v_goal_1069_);
                    if v_isShared_1106_ == 0 {
                        leanh::lean_ctor_set(v___x_1105_, 0, v___x_1158_);
                        v___x_1160_ = v___x_1105_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1161_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
                        v___x_1160_ = v_reuseFailAlloc_1161_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1118_ = leanh::lean_ctor_get(v_a_1114_, 0);
                leanh::lean_inc(v_fst_1118_);
                leanh::lean_dec(v_a_1114_);
                if leanh::lean_obj_tag(v_fst_1118_) == 1 {
                    leanh::lean_del_object(v___x_1116_);
                    v_val_1119_ = leanh::lean_ctor_get(v_fst_1118_, 0);
                    v_isSharedCheck_1145_ = (!leanh::lean_is_exclusive(v_fst_1118_)) as u8;
                    if v_isSharedCheck_1145_ == 0 {
                        v___x_1121_ = v_fst_1118_;
                        v_isShared_1122_ = v_isSharedCheck_1145_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1119_);
                        leanh::lean_dec(v_fst_1118_);
                        v___x_1121_ = leanh::lean_box(0);
                        v_isShared_1122_ = v_isSharedCheck_1145_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1118_);
                    if v_isShared_1117_ == 0 {
                        leanh::lean_ctor_set(v___x_1116_, 0, v___x_1094_);
                        v___x_1147_ = v___x_1116_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1094_);
                        v___x_1147_ = v_reuseFailAlloc_1148_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_1123_ = leanh::lean_ctor_get(v_val_1119_, 1);
                leanh::lean_inc_n(v_snd_1123_, 2);
                leanh::lean_dec(v_val_1119_);
                v___f_1124_ =
                    l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___closed__7;
                v___x_1125_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(v_snd_1123_, v___f_1124_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
                if leanh::lean_obj_tag(v___x_1125_) == 0 {
                    v_isSharedCheck_1135_ = (!leanh::lean_is_exclusive(v___x_1125_)) as u8;
                    if v_isSharedCheck_1135_ == 0 {
                        v_unused_1136_ = leanh::lean_ctor_get(v___x_1125_, 0);
                        leanh::lean_dec(v_unused_1136_);
                        v___x_1127_ = v___x_1125_;
                        v_isShared_1128_ = v_isSharedCheck_1135_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1125_);
                        v___x_1127_ = leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1135_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_1123_);
                    leanh::lean_del_object(v___x_1121_);
                    v_a_1137_ = leanh::lean_ctor_get(v___x_1125_, 0);
                    v_isSharedCheck_1144_ = (!leanh::lean_is_exclusive(v___x_1125_)) as u8;
                    if v_isSharedCheck_1144_ == 0 {
                        v___x_1139_ = v___x_1125_;
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1137_);
                        leanh::lean_dec(v___x_1125_);
                        v___x_1139_ = leanh::lean_box(0);
                        v_isShared_1140_ = v_isSharedCheck_1144_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1122_ == 0 {
                    leanh::lean_ctor_set(v___x_1121_, 0, v_snd_1123_);
                    v___x_1130_ = v___x_1121_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_snd_1123_);
                    v___x_1130_ = v_reuseFailAlloc_1134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1128_ == 0 {
                    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1130_);
                    v___x_1132_ = v___x_1127_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
                    v___x_1132_ = v_reuseFailAlloc_1133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1132_;
            }
            7 => {
                if v_isShared_1140_ == 0 {
                    v___x_1142_ = v___x_1139_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1143_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
                    v___x_1142_ = v_reuseFailAlloc_1143_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1142_;
            }
            9 => {
                return v___x_1147_;
            }
            10 => {
                if v_isShared_1153_ == 0 {
                    v___x_1155_ = v___x_1152_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
                    v___x_1155_ = v_reuseFailAlloc_1156_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1155_;
            }
            12 => {
                return v___x_1160_;
            }
            13 => {
                if v_isShared_1166_ == 0 {
                    v___x_1168_ = v___x_1165_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
                    v___x_1168_ = v_reuseFailAlloc_1169_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1168_;
            }
            15 => {
                if v_isShared_1174_ == 0 {
                    v___x_1176_ = v___x_1173_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
                    v___x_1176_ = v_reuseFailAlloc_1177_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1176_;
            }
            17 => {
                if v_isShared_1182_ == 0 {
                    v___x_1184_ = v___x_1181_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1184_;
            }
            19 => {
                if v_isShared_1190_ == 0 {
                    v___x_1192_ = v___x_1189_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1193_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1192_;
            }
            21 => {
                if v_isShared_1198_ == 0 {
                    v___x_1200_ = v___x_1197_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
                    v___x_1200_ = v_reuseFailAlloc_1201_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1200_;
            }
            23 => {
                if v_isShared_1206_ == 0 {
                    v___x_1208_ = v___x_1205_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
                    v___x_1208_ = v_reuseFailAlloc_1209_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1208_;
            }
            25 => {
                if v_isShared_1214_ == 0 {
                    v___x_1216_ = v___x_1213_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
                    v___x_1216_ = v_reuseFailAlloc_1217_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(
    mut v_goal_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
    mut v___y_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(
        v_goal_1219_,
        v___y_1220_,
        v___y_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
        v___y_1225_,
    );
    leanh::lean_dec(v___y_1225_);
    leanh::lean_dec_ref(v___y_1224_);
    leanh::lean_dec(v___y_1223_);
    leanh::lean_dec_ref(v___y_1222_);
    leanh::lean_dec(v___y_1221_);
    leanh::lean_dec_ref(v___y_1220_);
    return v_res_1227_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(
    mut v_00_u03b2_1236_: *mut leanh::LeanObject,
    mut v_m_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
    mut v_b_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_m_1237_, v_a_1238_, v_b_1239_);
    return v___x_1240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(
    mut v_as_1241_: *mut leanh::LeanObject,
    mut v_i_1242_: usize,
    mut v_stop_1243_: usize,
    mut v_b_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
    mut v___y_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_as_1241_, v_i_1242_, v_stop_1243_, v_b_1244_, v___y_1246_);
    return v___x_1252_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(
    mut v_as_1253_: *mut leanh::LeanObject,
    mut v_i_1254_: *mut leanh::LeanObject,
    mut v_stop_1255_: *mut leanh::LeanObject,
    mut v_b_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1264_: usize = 0;
    let mut v_stop_boxed_1265_: usize = 0;
    let mut v_res_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1264_ = leanh::lean_unbox_usize(v_i_1254_);
    leanh::lean_dec(v_i_1254_);
    v_stop_boxed_1265_ = leanh::lean_unbox_usize(v_stop_1255_);
    leanh::lean_dec(v_stop_1255_);
    v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_as_1253_, v_i_boxed_1264_, v_stop_boxed_1265_, v_b_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
    leanh::lean_dec(v___y_1262_);
    leanh::lean_dec_ref(v___y_1261_);
    leanh::lean_dec(v___y_1260_);
    leanh::lean_dec_ref(v___y_1259_);
    leanh::lean_dec(v___y_1258_);
    leanh::lean_dec_ref(v___y_1257_);
    leanh::lean_dec_ref(v_as_1253_);
    return v_res_1266_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(
    mut v_00_u03b2_1267_: *mut leanh::LeanObject,
    mut v_data_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___redArg(v_data_1268_);
    return v___x_1269_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1270_: *mut leanh::LeanObject,
    mut v_i_1271_: *mut leanh::LeanObject,
    mut v_source_1272_: *mut leanh::LeanObject,
    mut v_target_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1___redArg(v_i_1271_, v_source_1272_, v_target_1273_);
    return v___x_1274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1275_: *mut leanh::LeanObject,
    mut v_x_1276_: *mut leanh::LeanObject,
    mut v_x_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_spec__1_spec__3___redArg(v_x_1276_, v_x_1277_);
    return v___x_1278_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(
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
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(
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
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
}