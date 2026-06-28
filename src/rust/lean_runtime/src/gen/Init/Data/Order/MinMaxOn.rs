// Lean compiler output
// Module: Init.Data.Order.MinMaxOn
// Imports: Init.Data.Order.Opposite Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Order::Opposite::{
    initialize_Init_Data_Order_Opposite, runtime_initialize_Init_Data_Order_Opposite,
};
pub unsafe fn l_minOn___redArg(
    mut v_inst_41_: *mut crate::leanh::LeanObject,
    mut v_f_42_: *mut crate::leanh::LeanObject,
    mut v_x_43_: *mut crate::leanh::LeanObject,
    mut v_y_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: u8 = 0;
    crate::leanh::lean_inc(v_f_42_);
    crate::leanh::lean_inc(v_x_43_);
    v___x_45_ = crate::leanh::lean_apply_1(v_f_42_, v_x_43_);
    crate::leanh::lean_inc(v_y_44_);
    v___x_46_ = crate::leanh::lean_apply_1(v_f_42_, v_y_44_);
    v___x_47_ = crate::leanh::lean_apply_2(v_inst_41_, v___x_45_, v___x_46_);
    v___x_48_ = (crate::leanh::lean_unbox(v___x_47_) as u8);
    if v___x_48_ == 0 {
        crate::leanh::lean_dec(v_x_43_);
        return v_y_44_;
    } else {
        crate::leanh::lean_dec(v_y_44_);
        return v_x_43_;
    }
}
pub unsafe fn l_minOn(
    mut v_00_u03b2_49_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_50_: *mut crate::leanh::LeanObject,
    mut v_inst_51_: *mut crate::leanh::LeanObject,
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_f_53_: *mut crate::leanh::LeanObject,
    mut v_x_54_: *mut crate::leanh::LeanObject,
    mut v_y_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = l_minOn___redArg(v_inst_52_, v_f_53_, v_x_54_, v_y_55_);
    return v___x_56_;
}
pub unsafe fn l_maxOn___redArg___lam__0(
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_a_58_: *mut crate::leanh::LeanObject,
    mut v_b_59_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: u8 = 0;
    v___x_60_ = crate::leanh::lean_apply_2(v_inst_57_, v_b_59_, v_a_58_);
    v___x_61_ = (crate::leanh::lean_unbox(v___x_60_) as u8);
    return v___x_61_;
}
pub unsafe fn l_maxOn___redArg___lam__0___boxed(
    mut v_inst_62_: *mut crate::leanh::LeanObject,
    mut v_a_63_: *mut crate::leanh::LeanObject,
    mut v_b_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_65_ = l_maxOn___redArg___lam__0(v_inst_62_, v_a_63_, v_b_64_);
    v_r_66_ = crate::leanh::lean_box((v_res_65_) as usize);
    return v_r_66_;
}
pub unsafe fn l_maxOn___redArg(
    mut v_inst_67_: *mut crate::leanh::LeanObject,
    mut v_f_68_: *mut crate::leanh::LeanObject,
    mut v_x_69_: *mut crate::leanh::LeanObject,
    mut v_y_70_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_71_ = crate::leanh::lean_alloc_closure(
        l_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_71_, 0, v_inst_67_);
    v___x_72_ = l_minOn___redArg(v___f_71_, v_f_68_, v_x_69_, v_y_70_);
    return v___x_72_;
}
pub unsafe fn l_maxOn(
    mut v_00_u03b2_73_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_74_: *mut crate::leanh::LeanObject,
    mut v_i_75_: *mut crate::leanh::LeanObject,
    mut v_inst_76_: *mut crate::leanh::LeanObject,
    mut v_f_77_: *mut crate::leanh::LeanObject,
    mut v_x_78_: *mut crate::leanh::LeanObject,
    mut v_y_79_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_80_ = l_maxOn___redArg(v_inst_76_, v_f_77_, v_x_78_, v_y_79_);
    return v___x_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_MinMaxOn(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Opposite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_MinMaxOn(
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
pub unsafe fn initialize_Init_Data_Order_MinMaxOn(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Opposite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_MinMaxOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Order_MinMaxOn(builtin);
}
