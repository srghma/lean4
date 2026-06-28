// Lean compiler output
// Module: Init.Data.Vector.MapIdx
// Imports: Init.Data.Array.Basic Init.Data.Vector.Basic Init.Data.Vector.Attach Init.ByCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Vector::Attach::{
    initialize_Init_Data_Vector_Attach, runtime_initialize_Init_Data_Vector_Attach,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg(
    mut v_i_35_: *mut LeanObject,
    mut v_h__1_36_: *mut LeanObject,
    mut v_h__2_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_39_: u8 = 0;
    v_zero_38_ = lean_unsigned_to_nat(0);
    v_isZero_39_ = lean_nat_dec_eq(v_i_35_, v_zero_38_);
    if v_isZero_39_ == 1 {
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_37_);
        v___x_40_ = lean_apply_1(v_h__1_36_, lean_box(0));
        return v___x_40_;
    } else {
        let mut v_one_41_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_42_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_36_);
        v_one_41_ = lean_unsigned_to_nat(1);
        v_n_42_ = lean_nat_sub(v_i_35_, v_one_41_);
        v___x_43_ = lean_apply_2(v_h__2_37_, v_n_42_, lean_box(0));
        return v___x_43_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg___boxed(
    mut v_i_44_: *mut LeanObject,
    mut v_h__1_45_: *mut LeanObject,
    mut v_h__2_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_47_: *mut LeanObject = core::ptr::null_mut();
    v_res_47_ =
        l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___redArg(
            v_i_44_, v_h__1_45_, v_h__2_46_,
        );
    lean_dec(v_i_44_);
    return v_res_47_;
}
pub unsafe fn l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter(
    mut v_n_48_: *mut LeanObject,
    mut v_j_49_: *mut LeanObject,
    mut v_motive_50_: *mut LeanObject,
    mut v_i_51_: *mut LeanObject,
    mut v_inv_52_: *mut LeanObject,
    mut v_h__1_53_: *mut LeanObject,
    mut v_h__2_54_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_56_: u8 = 0;
    v_zero_55_ = lean_unsigned_to_nat(0);
    v_isZero_56_ = lean_nat_dec_eq(v_i_51_, v_zero_55_);
    if v_isZero_56_ == 1 {
        let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_54_);
        v___x_57_ = lean_apply_1(v_h__1_53_, lean_box(0));
        return v___x_57_;
    } else {
        let mut v_one_58_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_59_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_53_);
        v_one_58_ = lean_unsigned_to_nat(1);
        v_n_59_ = lean_nat_sub(v_i_51_, v_one_58_);
        v___x_60_ = lean_apply_2(v_h__2_54_, v_n_59_, lean_box(0));
        return v___x_60_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter___boxed(
    mut v_n_61_: *mut LeanObject,
    mut v_j_62_: *mut LeanObject,
    mut v_motive_63_: *mut LeanObject,
    mut v_i_64_: *mut LeanObject,
    mut v_inv_65_: *mut LeanObject,
    mut v_h__1_66_: *mut LeanObject,
    mut v_h__2_67_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_68_: *mut LeanObject = core::ptr::null_mut();
    v_res_68_ = l___private_Init_Data_Vector_MapIdx_0__Vector_mapFinIdxM_map_match__1_splitter(
        v_n_61_,
        v_j_62_,
        v_motive_63_,
        v_i_64_,
        v_inv_65_,
        v_h__1_66_,
        v_h__2_67_,
    );
    lean_dec(v_i_64_);
    lean_dec(v_j_62_);
    lean_dec(v_n_61_);
    return v_res_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Vector_MapIdx(builtin);
}
