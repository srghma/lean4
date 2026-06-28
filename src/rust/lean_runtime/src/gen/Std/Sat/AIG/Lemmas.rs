// Lean compiler output
// Module: Std.Sat.AIG.Lemmas
// Imports: Std.Sat.AIG.LawfulOperator Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulOperator::{
    initialize_Std_Sat_AIG_LawfulOperator, runtime_initialize_Std_Sat_AIG_LawfulOperator,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_37_: *mut LeanObject,
    mut v_h__1_38_: *mut LeanObject,
    mut v_h__2_39_: *mut LeanObject,
    mut v_h__3_40_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_37_) {
        0 => {
            let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_40_);
            lean_dec(v_h__2_39_);
            v___x_41_ = lean_apply_1(v_h__1_38_, lean_box(0));
            return v___x_41_;
        }
        1 => {
            let mut v_idx_42_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_40_);
            lean_dec(v_h__1_38_);
            v_idx_42_ = lean_ctor_get(v_x_37_, 0);
            lean_inc(v_idx_42_);
            lean_dec_ref_known(v_x_37_, 1);
            v___x_43_ = lean_apply_2(v_h__2_39_, v_idx_42_, lean_box(0));
            return v___x_43_;
        }
        _ => {
            let mut v_l_44_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_45_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_39_);
            lean_dec(v_h__1_38_);
            v_l_44_ = lean_ctor_get(v_x_37_, 0);
            lean_inc(v_l_44_);
            v_r_45_ = lean_ctor_get(v_x_37_, 1);
            lean_inc(v_r_45_);
            lean_dec_ref_known(v_x_37_, 2);
            v___x_46_ = lean_apply_3(v_h__3_40_, v_l_44_, v_r_45_, lean_box(0));
            return v___x_46_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_47_: *mut LeanObject,
    mut v_motive_48_: *mut LeanObject,
    mut v_x_49_: *mut LeanObject,
    mut v_h__1_50_: *mut LeanObject,
    mut v_h__2_51_: *mut LeanObject,
    mut v_h__3_52_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_49_) {
        0 => {
            let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_52_);
            lean_dec(v_h__2_51_);
            v___x_53_ = lean_apply_1(v_h__1_50_, lean_box(0));
            return v___x_53_;
        }
        1 => {
            let mut v_idx_54_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_52_);
            lean_dec(v_h__1_50_);
            v_idx_54_ = lean_ctor_get(v_x_49_, 0);
            lean_inc(v_idx_54_);
            lean_dec_ref_known(v_x_49_, 1);
            v___x_55_ = lean_apply_2(v_h__2_51_, v_idx_54_, lean_box(0));
            return v___x_55_;
        }
        _ => {
            let mut v_l_56_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_57_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_51_);
            lean_dec(v_h__1_50_);
            v_l_56_ = lean_ctor_get(v_x_49_, 0);
            lean_inc(v_l_56_);
            v_r_57_ = lean_ctor_get(v_x_49_, 1);
            lean_inc(v_r_57_);
            lean_dec_ref_known(v_x_49_, 2);
            v___x_58_ = lean_apply_3(v_h__3_52_, v_l_56_, v_r_57_, lean_box(0));
            return v___x_58_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter___redArg(
    mut v_decl_59_: *mut LeanObject,
    mut v_h__1_60_: *mut LeanObject,
    mut v_h__2_61_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_decl_59_) == 0 {
        let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_61_);
        v___x_62_ = lean_box(0);
        v___x_63_ = lean_apply_1(v_h__1_60_, v___x_62_);
        return v___x_63_;
    } else {
        let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_60_);
        v___x_64_ = lean_apply_2(v_h__2_61_, v_decl_59_, lean_box(0));
        return v___x_64_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter(
    mut v_00_u03b1_65_: *mut LeanObject,
    mut v_motive_66_: *mut LeanObject,
    mut v_decl_67_: *mut LeanObject,
    mut v_h__1_68_: *mut LeanObject,
    mut v_h__2_69_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_decl_67_) == 0 {
        let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_69_);
        v___x_70_ = lean_box(0);
        v___x_71_ = lean_apply_1(v_h__1_68_, v___x_70_);
        return v___x_71_;
    } else {
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_68_);
        v___x_72_ = lean_apply_2(v_h__2_69_, v_decl_67_, lean_box(0));
        return v___x_72_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulOperator(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Lemmas(builtin);
}
