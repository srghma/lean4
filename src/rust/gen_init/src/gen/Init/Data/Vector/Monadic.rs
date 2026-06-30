// Lean compiler output
// Module: Init.Data.Vector.Monadic
// Imports: Init.Data.Vector.Basic Init.Data.Vector.Attach Init.Data.Array.Monadic
use crate::r#gen::Init::Data::Array::Monadic::{
    initialize_Init_Data_Array_Monadic, runtime_initialize_Init_Data_Array_Monadic,
};
use crate::r#gen::Init::Data::Vector::Attach::{
    initialize_Init_Data_Vector_Attach, runtime_initialize_Init_Data_Vector_Attach,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_33_: *mut leanh::LeanObject,
    mut v_h__1_34_: *mut leanh::LeanObject,
    mut v_h__2_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_33_) == 0 {
        let mut v_a_36_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_34_);
        v_a_36_ = leanh::lean_ctor_get(v_b_33_, 0);
        leanh::lean_inc(v_a_36_);
        leanh::lean_dec_ref_known(v_b_33_, 1);
        v___x_37_ = leanh::lean_apply_1(v_h__2_35_, v_a_36_);
        return v___x_37_;
    } else {
        let mut v_a_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_35_);
        v_a_38_ = leanh::lean_ctor_get(v_b_33_, 0);
        leanh::lean_inc(v_a_38_);
        leanh::lean_dec_ref_known(v_b_33_, 1);
        v___x_39_ = leanh::lean_apply_1(v_h__1_34_, v_a_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_40_: *mut leanh::LeanObject,
    mut v_motive_41_: *mut leanh::LeanObject,
    mut v_b_42_: *mut leanh::LeanObject,
    mut v_h__1_43_: *mut leanh::LeanObject,
    mut v_h__2_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_42_) == 0 {
        let mut v_a_45_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_43_);
        v_a_45_ = leanh::lean_ctor_get(v_b_42_, 0);
        leanh::lean_inc(v_a_45_);
        leanh::lean_dec_ref_known(v_b_42_, 1);
        v___x_46_ = leanh::lean_apply_1(v_h__2_44_, v_a_45_);
        return v___x_46_;
    } else {
        let mut v_a_47_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_44_);
        v_a_47_ = leanh::lean_ctor_get(v_b_42_, 0);
        leanh::lean_inc(v_a_47_);
        leanh::lean_dec_ref_known(v_b_42_, 1);
        v___x_48_ = leanh::lean_apply_1(v_h__1_43_, v_a_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_49_: *mut leanh::LeanObject,
    mut v_h__1_50_: *mut leanh::LeanObject,
    mut v_h__2_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_49_) == 0 {
        let mut v_a_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_50_);
        v_a_52_ = leanh::lean_ctor_get(v_b_49_, 0);
        leanh::lean_inc(v_a_52_);
        leanh::lean_dec_ref_known(v_b_49_, 1);
        v___x_53_ = leanh::lean_apply_1(v_h__2_51_, v_a_52_);
        return v___x_53_;
    } else {
        let mut v_a_54_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_51_);
        v_a_54_ = leanh::lean_ctor_get(v_b_49_, 0);
        leanh::lean_inc(v_a_54_);
        leanh::lean_dec_ref_known(v_b_49_, 1);
        v___x_55_ = leanh::lean_apply_1(v_h__1_50_, v_a_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_56_: *mut leanh::LeanObject,
    mut v_motive_57_: *mut leanh::LeanObject,
    mut v_b_58_: *mut leanh::LeanObject,
    mut v_h__1_59_: *mut leanh::LeanObject,
    mut v_h__2_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_b_58_) == 0 {
        let mut v_a_61_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_59_);
        v_a_61_ = leanh::lean_ctor_get(v_b_58_, 0);
        leanh::lean_inc(v_a_61_);
        leanh::lean_dec_ref_known(v_b_58_, 1);
        v___x_62_ = leanh::lean_apply_1(v_h__2_60_, v_a_61_);
        return v___x_62_;
    } else {
        let mut v_a_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_60_);
        v_a_63_ = leanh::lean_ctor_get(v_b_58_, 0);
        leanh::lean_inc(v_a_63_);
        leanh::lean_dec_ref_known(v_b_58_, 1);
        v___x_64_ = leanh::lean_apply_1(v_h__1_59_, v_a_63_);
        return v___x_64_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Monadic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Monadic(
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
pub unsafe fn initialize_Init_Data_Vector_Monadic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Monadic(builtin);
}