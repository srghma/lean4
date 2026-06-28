// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchTheoremPtr
// Imports: Lean.Meta.Tactic.Grind.EMatchTheorem
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_shift_right, lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Prelude::lean_usize_dec_eq;
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_uint64, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instHashableEMatchTheoremPtr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHashableEMatchTheoremPtr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_instBEqEMatchTheoremPtr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instBEqEMatchTheoremPtr___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(
    mut v_a_34_: *mut LeanObject,
    mut v_b_35_: *mut LeanObject,
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
    mut v_a_39_: *mut LeanObject,
    mut v_b_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_41_: u8 = 0;
    let mut v_r_42_: *mut LeanObject = core::ptr::null_mut();
    v_res_41_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_39_, v_b_40_);
    lean_dec_ref(v_b_40_);
    lean_dec_ref(v_a_39_);
    v_r_42_ = lean_box((v_res_41_) as usize);
    return v_r_42_;
}
pub unsafe fn l_Lean_Meta_Grind_isSameEMatchTheoremPtr(
    mut v_a_43_: *mut LeanObject,
    mut v_b_44_: *mut LeanObject,
) -> u8 {
    let mut v___x_45_: u8 = 0;
    v___x_45_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_a_43_, v_b_44_);
    return v___x_45_;
}
pub unsafe fn l_Lean_Meta_Grind_isSameEMatchTheoremPtr___boxed(
    mut v_a_46_: *mut LeanObject,
    mut v_b_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_48_: u8 = 0;
    let mut v_r_49_: *mut LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Lean_Meta_Grind_isSameEMatchTheoremPtr(v_a_46_, v_b_47_);
    lean_dec_ref(v_b_47_);
    lean_dec_ref(v_a_46_);
    v_r_49_ = lean_box((v_res_48_) as usize);
    return v_r_49_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(
    mut v_thm_50_: *mut LeanObject,
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
    mut v_thm_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: u64 = 0;
    let mut v_r_57_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_55_);
    lean_dec_ref(v_thm_55_);
    v_r_57_ = lean_box_uint64(v_res_56_);
    return v_r_57_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr(mut v_thm_58_: *mut LeanObject) -> u64 {
    let mut v___x_59_: u64 = 0;
    v___x_59_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_thm_58_);
    return v___x_59_;
}
pub unsafe fn l_Lean_Meta_Grind_hashEMatchTheoremPtr___boxed(
    mut v_thm_60_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_61_: u64 = 0;
    let mut v_r_62_: *mut LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr(v_thm_60_);
    lean_dec_ref(v_thm_60_);
    v_r_62_ = lean_box_uint64(v_res_61_);
    return v_r_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
}
