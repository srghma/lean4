// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchTheoremPtr
// Imports: Lean.Meta.Tactic.Grind.EMatchTheorem
use crate::ffi::{lean_ptr_addr, lean_usize_dec_eq, lean_usize_shift_right, lean_usize_to_uint64};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
};
pub static l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instHashableEMatchTheoremPtr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremPtr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(
    mut v_a_34_: *mut leanh::LeanObject,
    mut v_b_35_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_36_: usize = 0;
    let mut v___x_37_: usize = 0;
    let mut v___x_38_: u8 = 0;
    v___x_36_ = lean_ptr_addr(v_a_34_);
    v___x_37_ = lean_ptr_addr(v_b_35_);
    v___x_38_ = lean_usize_dec_eq(v___x_36_, v___x_37_);
    return v___x_38_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed(
    mut v_a_39_: *mut leanh::LeanObject,
    mut v_b_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_41_: u8 = 0;
    let mut v_r_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_41_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_39_, v_b_40_);
    leanh::lean_dec_ref(v_b_40_);
    leanh::lean_dec_ref(v_a_39_);
    v_r_42_ = leanh::lean_box((v_res_41_) as usize);
    return v_r_42_;
}
pub unsafe fn l_Lean_Meta_Grind_isSameEMatchTheoremPtr(
    mut v_a_43_: *mut leanh::LeanObject,
    mut v_b_44_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_45_: u8 = 0;
    v___x_45_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_43_, v_b_44_);
    return v___x_45_;
}
pub unsafe fn l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(
    mut v_a_46_: *mut leanh::LeanObject,
    mut v_b_47_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_48_: u8 = 0;
    let mut v_r_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Lean_Meta_Grind_isSameEMatchTheoremPtr(v_a_46_, v_b_47_);
    leanh::lean_dec_ref(v_b_47_);
    leanh::lean_dec_ref(v_a_46_);
    v_r_49_ = leanh::lean_box((v_res_48_) as usize);
    return v_r_49_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(
    mut v_thm_50_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_51_: usize = 0;
    let mut v___x_52_: usize = 0;
    let mut v___x_53_: usize = 0;
    let mut v___x_54_: u64 = 0;
    v___x_51_ = lean_ptr_addr(v_thm_50_);
    v___x_52_ = 3usize;
    v___x_53_ = lean_usize_shift_right(v___x_51_, v___x_52_);
    v___x_54_ = lean_usize_to_uint64(v___x_53_);
    return v___x_54_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed(
    mut v_thm_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_56_: u64 = 0;
    let mut v_r_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_55_);
    leanh::lean_dec_ref(v_thm_55_);
    v_r_57_ = leanh::lean_box_uint64(v_res_56_);
    return v_r_57_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr(
    mut v_thm_58_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_59_: u64 = 0;
    v___x_59_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_58_);
    return v___x_59_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(
    mut v_thm_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_61_: u64 = 0;
    let mut v_r_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr(v_thm_60_);
    leanh::lean_dec_ref(v_thm_60_);
    v_r_62_ = leanh::lean_box_uint64(v_res_61_);
    return v_r_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
}