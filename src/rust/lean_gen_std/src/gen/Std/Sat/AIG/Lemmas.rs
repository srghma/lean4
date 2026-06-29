// Lean compiler output
// Module: Std.Sat.AIG.Lemmas
// Imports: Std.Sat.AIG.LawfulOperator Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulOperator::{
    initialize_Std_Sat_AIG_LawfulOperator, runtime_initialize_Std_Sat_AIG_LawfulOperator,
};
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_37_: *mut crate::leanh::LeanObject,
    mut v_h__1_38_: *mut crate::leanh::LeanObject,
    mut v_h__2_39_: *mut crate::leanh::LeanObject,
    mut v_h__3_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_37_) {
        0 => {
            let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_40_);
            crate::leanh::lean_dec(v_h__2_39_);
            v___x_41_ = crate::leanh::lean_apply_1(v_h__1_38_, crate::leanh::lean_box(0));
            return v___x_41_;
        }
        1 => {
            let mut v_idx_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_40_);
            crate::leanh::lean_dec(v_h__1_38_);
            v_idx_42_ = crate::leanh::lean_ctor_get(v_x_37_, 0);
            crate::leanh::lean_inc(v_idx_42_);
            crate::leanh::lean_dec_ref_known(v_x_37_, 1);
            v___x_43_ =
                crate::leanh::lean_apply_2(v_h__2_39_, v_idx_42_, crate::leanh::lean_box(0));
            return v___x_43_;
        }
        _ => {
            let mut v_l_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_39_);
            crate::leanh::lean_dec(v_h__1_38_);
            v_l_44_ = crate::leanh::lean_ctor_get(v_x_37_, 0);
            crate::leanh::lean_inc(v_l_44_);
            v_r_45_ = crate::leanh::lean_ctor_get(v_x_37_, 1);
            crate::leanh::lean_inc(v_r_45_);
            crate::leanh::lean_dec_ref_known(v_x_37_, 2);
            v___x_46_ =
                crate::leanh::lean_apply_3(v_h__3_40_, v_l_44_, v_r_45_, crate::leanh::lean_box(0));
            return v___x_46_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_47_: *mut crate::leanh::LeanObject,
    mut v_motive_48_: *mut crate::leanh::LeanObject,
    mut v_x_49_: *mut crate::leanh::LeanObject,
    mut v_h__1_50_: *mut crate::leanh::LeanObject,
    mut v_h__2_51_: *mut crate::leanh::LeanObject,
    mut v_h__3_52_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_49_) {
        0 => {
            let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_52_);
            crate::leanh::lean_dec(v_h__2_51_);
            v___x_53_ = crate::leanh::lean_apply_1(v_h__1_50_, crate::leanh::lean_box(0));
            return v___x_53_;
        }
        1 => {
            let mut v_idx_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_52_);
            crate::leanh::lean_dec(v_h__1_50_);
            v_idx_54_ = crate::leanh::lean_ctor_get(v_x_49_, 0);
            crate::leanh::lean_inc(v_idx_54_);
            crate::leanh::lean_dec_ref_known(v_x_49_, 1);
            v___x_55_ =
                crate::leanh::lean_apply_2(v_h__2_51_, v_idx_54_, crate::leanh::lean_box(0));
            return v___x_55_;
        }
        _ => {
            let mut v_l_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_51_);
            crate::leanh::lean_dec(v_h__1_50_);
            v_l_56_ = crate::leanh::lean_ctor_get(v_x_49_, 0);
            crate::leanh::lean_inc(v_l_56_);
            v_r_57_ = crate::leanh::lean_ctor_get(v_x_49_, 1);
            crate::leanh::lean_inc(v_r_57_);
            crate::leanh::lean_dec_ref_known(v_x_49_, 2);
            v___x_58_ =
                crate::leanh::lean_apply_3(v_h__3_52_, v_l_56_, v_r_57_, crate::leanh::lean_box(0));
            return v___x_58_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter___redArg(
    mut v_decl_59_: *mut crate::leanh::LeanObject,
    mut v_h__1_60_: *mut crate::leanh::LeanObject,
    mut v_h__2_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_59_) == 0 {
        let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_61_);
        v___x_62_ = crate::leanh::lean_box(0);
        v___x_63_ = crate::leanh::lean_apply_1(v_h__1_60_, v___x_62_);
        return v___x_63_;
    } else {
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_60_);
        v___x_64_ = crate::leanh::lean_apply_2(v_h__2_61_, v_decl_59_, crate::leanh::lean_box(0));
        return v___x_64_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Lemmas_0__Std_Sat_AIG_isConstant_match__1_splitter(
    mut v_00_u03b1_65_: *mut crate::leanh::LeanObject,
    mut v_motive_66_: *mut crate::leanh::LeanObject,
    mut v_decl_67_: *mut crate::leanh::LeanObject,
    mut v_h__1_68_: *mut crate::leanh::LeanObject,
    mut v_h__2_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_67_) == 0 {
        let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_69_);
        v___x_70_ = crate::leanh::lean_box(0);
        v___x_71_ = crate::leanh::lean_apply_1(v_h__1_68_, v___x_70_);
        return v___x_71_;
    } else {
        let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_68_);
        v___x_72_ = crate::leanh::lean_apply_2(v_h__2_69_, v_decl_67_, crate::leanh::lean_box(0));
        return v___x_72_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Lemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Lemmas(builtin);
}
