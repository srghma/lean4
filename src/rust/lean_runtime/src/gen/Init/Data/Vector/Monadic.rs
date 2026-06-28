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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_33_: *mut LeanObject,
    mut v_h__1_34_: *mut LeanObject,
    mut v_h__2_35_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_33_) == 0 {
        let mut v_a_36_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_34_);
        v_a_36_ = lean_ctor_get(v_b_33_, 0);
        lean_inc(v_a_36_);
        lean_dec_ref_known(v_b_33_, 1);
        v___x_37_ = lean_apply_1(v_h__2_35_, v_a_36_);
        return v___x_37_;
    } else {
        let mut v_a_38_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_35_);
        v_a_38_ = lean_ctor_get(v_b_33_, 0);
        lean_inc(v_a_38_);
        lean_dec_ref_known(v_b_33_, 1);
        v___x_39_ = lean_apply_1(v_h__1_34_, v_a_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_40_: *mut LeanObject,
    mut v_motive_41_: *mut LeanObject,
    mut v_b_42_: *mut LeanObject,
    mut v_h__1_43_: *mut LeanObject,
    mut v_h__2_44_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_42_) == 0 {
        let mut v_a_45_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_43_);
        v_a_45_ = lean_ctor_get(v_b_42_, 0);
        lean_inc(v_a_45_);
        lean_dec_ref_known(v_b_42_, 1);
        v___x_46_ = lean_apply_1(v_h__2_44_, v_a_45_);
        return v___x_46_;
    } else {
        let mut v_a_47_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_44_);
        v_a_47_ = lean_ctor_get(v_b_42_, 0);
        lean_inc(v_a_47_);
        lean_dec_ref_known(v_b_42_, 1);
        v___x_48_ = lean_apply_1(v_h__1_43_, v_a_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter___redArg(
    mut v_b_49_: *mut LeanObject,
    mut v_h__1_50_: *mut LeanObject,
    mut v_h__2_51_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_49_) == 0 {
        let mut v_a_52_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_50_);
        v_a_52_ = lean_ctor_get(v_b_49_, 0);
        lean_inc(v_a_52_);
        lean_dec_ref_known(v_b_49_, 1);
        v___x_53_ = lean_apply_1(v_h__2_51_, v_a_52_);
        return v___x_53_;
    } else {
        let mut v_a_54_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_51_);
        v_a_54_ = lean_ctor_get(v_b_49_, 0);
        lean_inc(v_a_54_);
        lean_dec_ref_known(v_b_49_, 1);
        v___x_55_ = lean_apply_1(v_h__1_50_, v_a_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter(
    mut v_00_u03b2_56_: *mut LeanObject,
    mut v_motive_57_: *mut LeanObject,
    mut v_b_58_: *mut LeanObject,
    mut v_h__1_59_: *mut LeanObject,
    mut v_h__2_60_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_58_) == 0 {
        let mut v_a_61_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_59_);
        v_a_61_ = lean_ctor_get(v_b_58_, 0);
        lean_inc(v_a_61_);
        lean_dec_ref_known(v_b_58_, 1);
        v___x_62_ = lean_apply_1(v_h__2_60_, v_a_61_);
        return v___x_62_;
    } else {
        let mut v_a_63_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_60_);
        v_a_63_ = lean_ctor_get(v_b_58_, 0);
        lean_inc(v_a_63_);
        lean_dec_ref_known(v_b_58_, 1);
        v___x_64_ = lean_apply_1(v_h__1_59_, v_a_63_);
        return v___x_64_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Monadic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Vector_Monadic(builtin);
}
