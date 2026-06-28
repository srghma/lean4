// Lean compiler output
// Module: Init.Data.Order.Lemmas
// Imports: Init.Data.Order.Factories Init.Data.Order.Factories Init.Classical Init.Data.BEq Init.Data.Bool
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Order::Factories::{
    initialize_Init_Data_Order_Factories, runtime_initialize_Init_Data_Order_Factories,
};
pub unsafe fn l_Std_instTransLeOfIsPreorder(
    mut v_00_u03b1_32_: *mut crate::leanh::LeanObject,
    mut v_inst_33_: *mut crate::leanh::LeanObject,
    mut v_inst_34_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_35_ = crate::leanh::lean_box(0);
    return v___x_35_;
}
pub unsafe fn l_Std_instTransLtOfLeOfLawfulOrderLT(
    mut v_00_u03b1_36_: *mut crate::leanh::LeanObject,
    mut v_inst_37_: *mut crate::leanh::LeanObject,
    mut v_inst_38_: *mut crate::leanh::LeanObject,
    mut v_inst_39_: *mut crate::leanh::LeanObject,
    mut v_inst_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = crate::leanh::lean_box(0);
    return v___x_41_;
}
pub unsafe fn l_Std_instTransNotLtOfLawfulOrderLTOfTotalOfLe(
    mut v_00_u03b1_42_: *mut crate::leanh::LeanObject,
    mut v_x_43_: *mut crate::leanh::LeanObject,
    mut v_inst_44_: *mut crate::leanh::LeanObject,
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
    mut v_inst_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_48_ = crate::leanh::lean_box(0);
    return v___x_48_;
}
pub unsafe fn l_Classical_Order_instLT(
    mut v_00_u03b1_49_: *mut crate::leanh::LeanObject,
    mut v_inst_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = crate::leanh::lean_box(0);
    return v___x_51_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0(
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_a_53_: *mut crate::leanh::LeanObject,
    mut v_b_54_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_55_ = crate::leanh::lean_apply_2(v_inst_52_, v_a_53_, v_b_54_);
    return v___x_55_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr___redArg(
    mut v_inst_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_57_ = crate::leanh::lean_alloc_closure(
        l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_57_, 0, v_inst_56_);
    return v___f_57_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr(
    mut v_00_u03b1_58_: *mut crate::leanh::LeanObject,
    mut v_inst_59_: *mut crate::leanh::LeanObject,
    mut v_inst_60_: *mut crate::leanh::LeanObject,
    mut v_P_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_62_ = crate::leanh::lean_alloc_closure(
        l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_62_, 0, v_inst_59_);
    return v___f_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_Lemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Factories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Factories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Order_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Factories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Factories(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Order_Lemmas(builtin);
}
