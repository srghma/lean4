// Lean compiler output
// Module: Init.Data.Order.MinMaxOn
// Imports: Init.Data.Order.Opposite Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::Order::Opposite::{
    initialize_Init_Data_Order_Opposite, runtime_initialize_Init_Data_Order_Opposite,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_box,
    lean_closure_set, lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_minOn___redArg(
    mut v_inst_41_: *mut LeanObject,
    mut v_f_42_: *mut LeanObject,
    mut v_x_43_: *mut LeanObject,
    mut v_y_44_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: u8 = 0;
    lean_inc(v_f_42_);
    lean_inc(v_x_43_);
    v___x_45_ = lean_apply_1(v_f_42_, v_x_43_);
    lean_inc(v_y_44_);
    v___x_46_ = lean_apply_1(v_f_42_, v_y_44_);
    v___x_47_ = lean_apply_2(v_inst_41_, v___x_45_, v___x_46_);
    v___x_48_ = (lean_unbox(v___x_47_) as u8);
    if v___x_48_ == 0 {
        lean_dec(v_x_43_);
        return v_y_44_;
    } else {
        lean_dec(v_y_44_);
        return v_x_43_;
    }
}
pub unsafe fn l_minOn(
    mut v_00_u03b2_49_: *mut LeanObject,
    mut v_00_u03b1_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
    mut v_inst_52_: *mut LeanObject,
    mut v_f_53_: *mut LeanObject,
    mut v_x_54_: *mut LeanObject,
    mut v_y_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
    v___x_56_ = l_minOn___redArg(v_inst_52_, v_f_53_, v_x_54_, v_y_55_);
    return v___x_56_;
}
pub unsafe fn l_maxOn___redArg___lam__0(
    mut v_inst_57_: *mut LeanObject,
    mut v_a_58_: *mut LeanObject,
    mut v_b_59_: *mut LeanObject,
) -> u8 {
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: u8 = 0;
    v___x_60_ = lean_apply_2(v_inst_57_, v_b_59_, v_a_58_);
    v___x_61_ = (lean_unbox(v___x_60_) as u8);
    return v___x_61_;
}
pub unsafe fn l_maxOn___redArg___lam__0___boxed(
    mut v_inst_62_: *mut LeanObject,
    mut v_a_63_: *mut LeanObject,
    mut v_b_64_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_65_: u8 = 0;
    let mut v_r_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_65_ = l_maxOn___redArg___lam__0(v_inst_62_, v_a_63_, v_b_64_);
    v_r_66_ = lean_box((v_res_65_) as usize);
    return v_r_66_;
}
pub unsafe fn l_maxOn___redArg(
    mut v_inst_67_: *mut LeanObject,
    mut v_f_68_: *mut LeanObject,
    mut v_x_69_: *mut LeanObject,
    mut v_y_70_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_71_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
    v___f_71_ = lean_alloc_closure(
        l_maxOn___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_71_, 0, v_inst_67_);
    v___x_72_ = l_minOn___redArg(v___f_71_, v_f_68_, v_x_69_, v_y_70_);
    return v___x_72_;
}
pub unsafe fn l_maxOn(
    mut v_00_u03b2_73_: *mut LeanObject,
    mut v_00_u03b1_74_: *mut LeanObject,
    mut v_i_75_: *mut LeanObject,
    mut v_inst_76_: *mut LeanObject,
    mut v_f_77_: *mut LeanObject,
    mut v_x_78_: *mut LeanObject,
    mut v_y_79_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
    v___x_80_ = l_maxOn___redArg(v_inst_76_, v_f_77_, v_x_78_, v_y_79_);
    return v___x_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Opposite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Order_MinMaxOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Opposite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_MinMaxOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Order_MinMaxOn(builtin);
}
