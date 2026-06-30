// Lean compiler output
// Module: Init.Data.Cast
// Imports: Init.Coe
use crate::r#gen::Init::Coe::{initialize_Init_Coe, runtime_initialize_Init_Coe};
pub static l_instNatCastNat___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instNatCastNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instNatCastNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNatCastNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instNatCastNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instNatCastNat___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_instNatCastNat___lam__0(
    mut v_n_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_23_);
    return v_n_23_;
}
pub unsafe fn l_instNatCastNat___lam__0___boxed(
    mut v_n_24_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_25_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_25_ = l_instNatCastNat___lam__0(v_n_24_);
    leanh::lean_dec(v_n_24_);
    return v_res_25_;
}
pub unsafe fn l_Nat_cast___redArg(
    mut v_inst_28_: *mut leanh::LeanObject,
    mut v_a_29_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = leanh::lean_apply_1(v_inst_28_, v_a_29_);
    return v___x_30_;
}
pub unsafe fn l_Nat_cast(
    mut v_R_31_: *mut leanh::LeanObject,
    mut v_inst_32_: *mut leanh::LeanObject,
    mut v_a_33_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_34_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_34_ = leanh::lean_apply_1(v_inst_32_, v_a_33_);
    return v___x_34_;
}
pub unsafe fn l_instCoeTailNatOfNatCast___redArg(
    mut v_inst_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36_ = leanh::lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_36_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_36_, 1, v_inst_35_);
    return v___x_36_;
}
pub unsafe fn l_instCoeTailNatOfNatCast(
    mut v_R_37_: *mut leanh::LeanObject,
    mut v_inst_38_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_39_ = leanh::lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_39_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_39_, 1, v_inst_38_);
    return v___x_39_;
}
pub unsafe fn l_instCoeHTCTNatOfNatCast___redArg(
    mut v_inst_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = leanh::lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_41_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_41_, 1, v_inst_40_);
    return v___x_41_;
}
pub unsafe fn l_instCoeHTCTNatOfNatCast(
    mut v_R_42_: *mut leanh::LeanObject,
    mut v_inst_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_44_ = leanh::lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___x_44_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_44_, 1, v_inst_43_);
    return v___x_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Cast(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Cast(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Cast(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Cast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Cast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Cast(builtin);
}