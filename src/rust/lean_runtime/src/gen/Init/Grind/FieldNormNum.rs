// Lean compiler output
// Module: Init.Grind.FieldNormNum
// Imports: Init.Grind.Ring.Field Init.Data.Rat.Basic Init.Data.Rat.Lemmas Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Rat::Basic::{
    initialize_Init_Data_Rat_Basic, runtime_initialize_Init_Data_Rat_Basic,
};
use crate::r#gen::Init::Data::Rat::Lemmas::{
    initialize_Init_Data_Rat_Lemmas, runtime_initialize_Init_Data_Rat_Lemmas,
};
use crate::r#gen::Init::Grind::Ring::Field::{
    initialize_Init_Grind_Ring_Field, runtime_initialize_Init_Grind_Ring_Field,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get,
    lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Lean_Grind_Field_NormNum_ofRat___redArg(
    mut v_inst_26_: *mut LeanObject,
    mut v_r_27_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommRing_28_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toDiv_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCast_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCast_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    v_toCommRing_28_ = lean_ctor_get(v_inst_26_, 0);
    lean_inc_ref(v_toCommRing_28_);
    v_toSemiring_29_ = lean_ctor_get(v_toCommRing_28_, 0);
    lean_inc_ref(v_toSemiring_29_);
    v_toDiv_30_ = lean_ctor_get(v_inst_26_, 2);
    lean_inc(v_toDiv_30_);
    lean_dec_ref(v_inst_26_);
    v_intCast_31_ = lean_ctor_get(v_toCommRing_28_, 3);
    lean_inc(v_intCast_31_);
    lean_dec_ref(v_toCommRing_28_);
    v_num_32_ = lean_ctor_get(v_r_27_, 0);
    lean_inc(v_num_32_);
    v_den_33_ = lean_ctor_get(v_r_27_, 1);
    lean_inc(v_den_33_);
    lean_dec_ref(v_r_27_);
    v_natCast_34_ = lean_ctor_get(v_toSemiring_29_, 2);
    lean_inc(v_natCast_34_);
    lean_dec_ref(v_toSemiring_29_);
    v___x_35_ = lean_apply_1(v_intCast_31_, v_num_32_);
    v___x_36_ = lean_apply_1(v_natCast_34_, v_den_33_);
    v___x_37_ = lean_apply_2(v_toDiv_30_, v___x_35_, v___x_36_);
    return v___x_37_;
}
pub unsafe fn l_Lean_Grind_Field_NormNum_ofRat(
    mut v_00_u03b1_38_: *mut LeanObject,
    mut v_inst_39_: *mut LeanObject,
    mut v_r_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toCommRing_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemiring_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toDiv_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intCast_44_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCast_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    v_toCommRing_41_ = lean_ctor_get(v_inst_39_, 0);
    lean_inc_ref(v_toCommRing_41_);
    v_toSemiring_42_ = lean_ctor_get(v_toCommRing_41_, 0);
    lean_inc_ref(v_toSemiring_42_);
    v_toDiv_43_ = lean_ctor_get(v_inst_39_, 2);
    lean_inc(v_toDiv_43_);
    lean_dec_ref(v_inst_39_);
    v_intCast_44_ = lean_ctor_get(v_toCommRing_41_, 3);
    lean_inc(v_intCast_44_);
    lean_dec_ref(v_toCommRing_41_);
    v_num_45_ = lean_ctor_get(v_r_40_, 0);
    lean_inc(v_num_45_);
    v_den_46_ = lean_ctor_get(v_r_40_, 1);
    lean_inc(v_den_46_);
    lean_dec_ref(v_r_40_);
    v_natCast_47_ = lean_ctor_get(v_toSemiring_42_, 2);
    lean_inc(v_natCast_47_);
    lean_dec_ref(v_toSemiring_42_);
    v___x_48_ = lean_apply_1(v_intCast_44_, v_num_45_);
    v___x_49_ = lean_apply_1(v_natCast_47_, v_den_46_);
    v___x_50_ = lean_apply_2(v_toDiv_43_, v___x_48_, v___x_49_);
    return v___x_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_FieldNormNum(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_FieldNormNum(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_FieldNormNum(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Field(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_FieldNormNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_FieldNormNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_FieldNormNum(builtin);
}
