// Lean compiler output
// Module: Lean.Util.FindMVar
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasExprMVar, runtime_initialize_Lean_Expr,
};
pub unsafe fn l_Lean_FindMVar_main(
    mut v_p_49_: *mut leanh::LeanObject,
    mut v_x_50_: *mut leanh::LeanObject,
    mut v_a_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_66_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_76_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: u8 = 0;
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_50_) {
                11 => {
                    v_struct_58_ = leanh::lean_ctor_get(v_x_50_, 2);
                    leanh::lean_inc_ref(v_struct_58_);
                    leanh::lean_dec_ref_known(v_x_50_, 3);
                    v___x_59_ = l_Lean_FindMVar_visit(v_p_49_, v_struct_58_, v_a_51_);
                    return v___x_59_;
                }
                7 => {
                    v_binderType_60_ = leanh::lean_ctor_get(v_x_50_, 1);
                    leanh::lean_inc_ref(v_binderType_60_);
                    v_body_61_ = leanh::lean_ctor_get(v_x_50_, 2);
                    leanh::lean_inc_ref(v_body_61_);
                    leanh::lean_dec_ref_known(v_x_50_, 3);
                    v_d_53_ = v_binderType_60_;
                    v_b_54_ = v_body_61_;
                    v___y_55_ = v_a_51_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_62_ = leanh::lean_ctor_get(v_x_50_, 1);
                    leanh::lean_inc_ref(v_binderType_62_);
                    v_body_63_ = leanh::lean_ctor_get(v_x_50_, 2);
                    leanh::lean_inc_ref(v_body_63_);
                    leanh::lean_dec_ref_known(v_x_50_, 3);
                    v_d_53_ = v_binderType_62_;
                    v_b_54_ = v_body_63_;
                    v___y_55_ = v_a_51_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_64_ = leanh::lean_ctor_get(v_x_50_, 1);
                    leanh::lean_inc_ref(v_type_64_);
                    v_value_65_ = leanh::lean_ctor_get(v_x_50_, 2);
                    leanh::lean_inc_ref(v_value_65_);
                    v_body_66_ = leanh::lean_ctor_get(v_x_50_, 3);
                    leanh::lean_inc_ref(v_body_66_);
                    leanh::lean_dec_ref_known(v_x_50_, 4);
                    leanh::lean_inc_ref_n(v_p_49_, 2);
                    v___x_67_ = l_Lean_FindMVar_visit(v_p_49_, v_type_64_, v_a_51_);
                    v___x_68_ = l_Lean_FindMVar_visit(v_p_49_, v_value_65_, v___x_67_);
                    leanh::lean_dec(v___x_67_);
                    v___x_69_ = l_Lean_FindMVar_visit(v_p_49_, v_body_66_, v___x_68_);
                    leanh::lean_dec(v___x_68_);
                    return v___x_69_;
                }
                5 => {
                    v_fn_70_ = leanh::lean_ctor_get(v_x_50_, 0);
                    leanh::lean_inc_ref(v_fn_70_);
                    v_arg_71_ = leanh::lean_ctor_get(v_x_50_, 1);
                    leanh::lean_inc_ref(v_arg_71_);
                    leanh::lean_dec_ref_known(v_x_50_, 2);
                    leanh::lean_inc_ref(v_p_49_);
                    v___x_72_ = l_Lean_FindMVar_visit(v_p_49_, v_fn_70_, v_a_51_);
                    v___x_73_ = l_Lean_FindMVar_visit(v_p_49_, v_arg_71_, v___x_72_);
                    leanh::lean_dec(v___x_72_);
                    return v___x_73_;
                }
                10 => {
                    v_expr_74_ = leanh::lean_ctor_get(v_x_50_, 1);
                    leanh::lean_inc_ref(v_expr_74_);
                    leanh::lean_dec_ref_known(v_x_50_, 2);
                    v___x_75_ = l_Lean_FindMVar_visit(v_p_49_, v_expr_74_, v_a_51_);
                    return v___x_75_;
                }
                2 => {
                    if leanh::lean_obj_tag(v_a_51_) == 0 {
                        v_mvarId_76_ = leanh::lean_ctor_get(v_x_50_, 0);
                        leanh::lean_inc_n(v_mvarId_76_, 2);
                        leanh::lean_dec_ref_known(v_x_50_, 1);
                        v___x_77_ = leanh::lean_apply_1(v_p_49_, v_mvarId_76_);
                        v___x_78_ = (leanh::lean_unbox(v___x_77_) as u8);
                        if v___x_78_ == 0 {
                            leanh::lean_dec(v_mvarId_76_);
                            return v_a_51_;
                        } else {
                            v___x_79_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_79_, 0, v_mvarId_76_);
                            return v___x_79_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_50_, 1);
                        leanh::lean_dec_ref(v_p_49_);
                        leanh::lean_inc_ref(v_a_51_);
                        return v_a_51_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_x_50_);
                    leanh::lean_dec_ref(v_p_49_);
                    leanh::lean_inc(v_a_51_);
                    return v_a_51_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_p_49_);
                v___x_56_ = l_Lean_FindMVar_visit(v_p_49_, v_d_53_, v___y_55_);
                v___x_57_ = l_Lean_FindMVar_visit(v_p_49_, v_b_54_, v___x_56_);
                leanh::lean_dec(v___x_56_);
                return v___x_57_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindMVar_visit(
    mut v_p_80_: *mut leanh::LeanObject,
    mut v_e_81_: *mut leanh::LeanObject,
    mut v_s_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_s_82_) == 0 {
        let mut v___x_83_: u8 = 0;
        v___x_83_ = l_Lean_Expr_hasExprMVar(v_e_81_);
        if v___x_83_ == 0 {
            leanh::lean_dec_ref(v_e_81_);
            leanh::lean_dec_ref(v_p_80_);
            return v_s_82_;
        } else {
            let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_84_ = l_Lean_FindMVar_main(v_p_80_, v_e_81_, v_s_82_);
            return v___x_84_;
        }
    } else {
        leanh::lean_dec_ref(v_e_81_);
        leanh::lean_dec_ref(v_p_80_);
        leanh::lean_inc_ref(v_s_82_);
        return v_s_82_;
    }
}
pub unsafe fn l_Lean_FindMVar_visit___boxed(
    mut v_p_85_: *mut leanh::LeanObject,
    mut v_e_86_: *mut leanh::LeanObject,
    mut v_s_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_88_ = l_Lean_FindMVar_visit(v_p_85_, v_e_86_, v_s_87_);
    leanh::lean_dec(v_s_87_);
    return v_res_88_;
}
pub unsafe fn l_Lean_FindMVar_main___boxed(
    mut v_p_89_: *mut leanh::LeanObject,
    mut v_x_90_: *mut leanh::LeanObject,
    mut v_a_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l_Lean_FindMVar_main(v_p_89_, v_x_90_, v_a_91_);
    leanh::lean_dec(v_a_91_);
    return v_res_92_;
}
pub unsafe fn l_Lean_Expr_findMVar_x3f(
    mut v_e_93_: *mut leanh::LeanObject,
    mut v_p_94_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_95_ = leanh::lean_box(0);
    v___x_96_ = l_Lean_FindMVar_main(v_p_94_, v_e_93_, v___x_95_);
    return v___x_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FindMVar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FindMVar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FindMVar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindMVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FindMVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FindMVar(builtin);
}