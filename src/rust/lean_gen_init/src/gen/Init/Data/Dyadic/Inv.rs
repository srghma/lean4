// Lean compiler output
// Module: Init.Data.Dyadic.Inv
// Imports: Init.Data.Dyadic.Basic Init.Data.Int.Order Init.Data.Rat.Lemmas
use crate::r#gen::Init::Data::Dyadic::Basic::{
    initialize_Init_Data_Dyadic_Basic, l_Dyadic_toRat, l_Rat_toDyadic,
    runtime_initialize_Init_Data_Dyadic_Basic,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_inv};
use crate::r#gen::Init::Data::Rat::Lemmas::{
    initialize_Init_Data_Rat_Lemmas, runtime_initialize_Init_Data_Rat_Lemmas,
};
pub unsafe fn l_Dyadic_invAtPrec(
    mut v_x_20_: *mut crate::leanh::LeanObject,
    mut v_prec_21_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_20_) == 0 {
        return v_x_20_;
    } else {
        let mut v___x_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_22_ = l_Dyadic_toRat(v_x_20_);
        v___x_23_ = l_Rat_inv(v___x_22_);
        v___x_24_ = l_Rat_toDyadic(v___x_23_, v_prec_21_);
        return v___x_24_;
    }
}
pub unsafe fn l_Dyadic_invAtPrec___boxed(
    mut v_x_25_: *mut crate::leanh::LeanObject,
    mut v_prec_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_27_ = l_Dyadic_invAtPrec(v_x_25_, v_prec_26_);
    crate::leanh::lean_dec(v_prec_26_);
    return v_res_27_;
}
pub unsafe fn l_Dyadic_divAtPrec(
    mut v_a_28_: *mut crate::leanh::LeanObject,
    mut v_b_29_: *mut crate::leanh::LeanObject,
    mut v_prec_30_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_29_) == 0 {
        crate::leanh::lean_dec(v_a_28_);
        return v_b_29_;
    } else {
        let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_31_ = l_Dyadic_toRat(v_a_28_);
        v___x_32_ = l_Dyadic_toRat(v_b_29_);
        v___x_33_ = l_Rat_div(v___x_31_, v___x_32_);
        crate::leanh::lean_dec_ref(v___x_31_);
        v___x_34_ = l_Rat_toDyadic(v___x_33_, v_prec_30_);
        return v___x_34_;
    }
}
pub unsafe fn l_Dyadic_divAtPrec___boxed(
    mut v_a_35_: *mut crate::leanh::LeanObject,
    mut v_b_36_: *mut crate::leanh::LeanObject,
    mut v_prec_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_38_ = l_Dyadic_divAtPrec(v_a_35_, v_b_36_, v_prec_37_);
    crate::leanh::lean_dec(v_prec_37_);
    return v_res_38_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Dyadic_Inv(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Dyadic_Inv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Dyadic_Inv(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Dyadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Dyadic_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Dyadic_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Dyadic_Inv(builtin);
}
