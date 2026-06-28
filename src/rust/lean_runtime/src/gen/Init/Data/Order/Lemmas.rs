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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_instTransLeOfIsPreorder(
    mut v_00_u03b1_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_inst_34_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    v___x_35_ = lean_box(0);
    return v___x_35_;
}
pub unsafe fn l_Std_instTransLtOfLeOfLawfulOrderLT(
    mut v_00_u03b1_36_: *mut LeanObject,
    mut v_inst_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
    mut v_inst_39_: *mut LeanObject,
    mut v_inst_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    v___x_41_ = lean_box(0);
    return v___x_41_;
}
pub unsafe fn l_Std_instTransNotLtOfLawfulOrderLTOfTotalOfLe(
    mut v_00_u03b1_42_: *mut LeanObject,
    mut v_x_43_: *mut LeanObject,
    mut v_inst_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
    mut v_inst_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    v___x_48_ = lean_box(0);
    return v___x_48_;
}
pub unsafe fn l_Classical_Order_instLT(
    mut v_00_u03b1_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    v___x_51_ = lean_box(0);
    return v___x_51_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0(
    mut v_inst_52_: *mut LeanObject,
    mut v_a_53_: *mut LeanObject,
    mut v_b_54_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    v___x_55_ = lean_apply_2(v_inst_52_, v_a_53_, v_b_54_);
    return v___x_55_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr___redArg(
    mut v_inst_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_57_: *mut LeanObject = core::ptr::null_mut();
    v___f_57_ = lean_alloc_closure(
        l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_57_, 0, v_inst_56_);
    return v___f_57_;
}
pub unsafe fn l_Std_instMaxSubtypeOfMaxEqOr(
    mut v_00_u03b1_58_: *mut LeanObject,
    mut v_inst_59_: *mut LeanObject,
    mut v_inst_60_: *mut LeanObject,
    mut v_P_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_62_: *mut LeanObject = core::ptr::null_mut();
    v___f_62_ = lean_alloc_closure(
        l_Std_instMaxSubtypeOfMaxEqOr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_62_, 0, v_inst_59_);
    return v___f_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Factories(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Order_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Factories(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Order_Lemmas(builtin);
}
