// Lean compiler output
// Module: Lean.Util.FindMVar
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasExprMVar, runtime_initialize_Lean_Expr,
};
pub unsafe fn l_Lean_FindMVar_main(
    mut v_p_49_: *mut crate::leanh::LeanObject,
    mut v_x_50_: *mut crate::leanh::LeanObject,
    mut v_a_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_78_: u8 = 0;
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_50_) {
                11 => {
                    v_struct_58_ = crate::leanh::lean_ctor_get(v_x_50_, 2);
                    crate::leanh::lean_inc_ref(v_struct_58_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 3);
                    v___x_59_ = l_Lean_FindMVar_visit(v_p_49_, v_struct_58_, v_a_51_);
                    return v___x_59_;
                }
                7 => {
                    v_binderType_60_ = crate::leanh::lean_ctor_get(v_x_50_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_60_);
                    v_body_61_ = crate::leanh::lean_ctor_get(v_x_50_, 2);
                    crate::leanh::lean_inc_ref(v_body_61_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 3);
                    v_d_53_ = v_binderType_60_;
                    v_b_54_ = v_body_61_;
                    v___y_55_ = v_a_51_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_62_ = crate::leanh::lean_ctor_get(v_x_50_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_62_);
                    v_body_63_ = crate::leanh::lean_ctor_get(v_x_50_, 2);
                    crate::leanh::lean_inc_ref(v_body_63_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 3);
                    v_d_53_ = v_binderType_62_;
                    v_b_54_ = v_body_63_;
                    v___y_55_ = v_a_51_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_64_ = crate::leanh::lean_ctor_get(v_x_50_, 1);
                    crate::leanh::lean_inc_ref(v_type_64_);
                    v_value_65_ = crate::leanh::lean_ctor_get(v_x_50_, 2);
                    crate::leanh::lean_inc_ref(v_value_65_);
                    v_body_66_ = crate::leanh::lean_ctor_get(v_x_50_, 3);
                    crate::leanh::lean_inc_ref(v_body_66_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 4);
                    crate::leanh::lean_inc_ref_n(v_p_49_, 2);
                    v___x_67_ = l_Lean_FindMVar_visit(v_p_49_, v_type_64_, v_a_51_);
                    v___x_68_ = l_Lean_FindMVar_visit(v_p_49_, v_value_65_, v___x_67_);
                    crate::leanh::lean_dec(v___x_67_);
                    v___x_69_ = l_Lean_FindMVar_visit(v_p_49_, v_body_66_, v___x_68_);
                    crate::leanh::lean_dec(v___x_68_);
                    return v___x_69_;
                }
                5 => {
                    v_fn_70_ = crate::leanh::lean_ctor_get(v_x_50_, 0);
                    crate::leanh::lean_inc_ref(v_fn_70_);
                    v_arg_71_ = crate::leanh::lean_ctor_get(v_x_50_, 1);
                    crate::leanh::lean_inc_ref(v_arg_71_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 2);
                    crate::leanh::lean_inc_ref(v_p_49_);
                    v___x_72_ = l_Lean_FindMVar_visit(v_p_49_, v_fn_70_, v_a_51_);
                    v___x_73_ = l_Lean_FindMVar_visit(v_p_49_, v_arg_71_, v___x_72_);
                    crate::leanh::lean_dec(v___x_72_);
                    return v___x_73_;
                }
                10 => {
                    v_expr_74_ = crate::leanh::lean_ctor_get(v_x_50_, 1);
                    crate::leanh::lean_inc_ref(v_expr_74_);
                    crate::leanh::lean_dec_ref_known(v_x_50_, 2);
                    v___x_75_ = l_Lean_FindMVar_visit(v_p_49_, v_expr_74_, v_a_51_);
                    return v___x_75_;
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_a_51_) == 0 {
                        v_mvarId_76_ = crate::leanh::lean_ctor_get(v_x_50_, 0);
                        crate::leanh::lean_inc_n(v_mvarId_76_, 2);
                        crate::leanh::lean_dec_ref_known(v_x_50_, 1);
                        v___x_77_ = crate::leanh::lean_apply_1(v_p_49_, v_mvarId_76_);
                        v___x_78_ = (crate::leanh::lean_unbox(v___x_77_) as u8);
                        if v___x_78_ == 0 {
                            crate::leanh::lean_dec(v_mvarId_76_);
                            return v_a_51_;
                        } else {
                            v___x_79_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_79_, 0, v_mvarId_76_);
                            return v___x_79_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_50_, 1);
                        crate::leanh::lean_dec_ref(v_p_49_);
                        crate::leanh::lean_inc_ref(v_a_51_);
                        return v_a_51_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_50_);
                    crate::leanh::lean_dec_ref(v_p_49_);
                    crate::leanh::lean_inc(v_a_51_);
                    return v_a_51_;
                }
            },
            1 => {
                crate::leanh::lean_inc_ref(v_p_49_);
                v___x_56_ = l_Lean_FindMVar_visit(v_p_49_, v_d_53_, v___y_55_);
                v___x_57_ = l_Lean_FindMVar_visit(v_p_49_, v_b_54_, v___x_56_);
                crate::leanh::lean_dec(v___x_56_);
                return v___x_57_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindMVar_visit(
    mut v_p_80_: *mut crate::leanh::LeanObject,
    mut v_e_81_: *mut crate::leanh::LeanObject,
    mut v_s_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_s_82_) == 0 {
        let mut v___x_83_: u8 = 0;
        v___x_83_ = l_Lean_Expr_hasExprMVar(v_e_81_);
        if v___x_83_ == 0 {
            crate::leanh::lean_dec_ref(v_e_81_);
            crate::leanh::lean_dec_ref(v_p_80_);
            return v_s_82_;
        } else {
            let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_84_ = l_Lean_FindMVar_main(v_p_80_, v_e_81_, v_s_82_);
            return v___x_84_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_81_);
        crate::leanh::lean_dec_ref(v_p_80_);
        crate::leanh::lean_inc_ref(v_s_82_);
        return v_s_82_;
    }
}
pub unsafe fn l_Lean_FindMVar_visit___boxed(
    mut v_p_85_: *mut crate::leanh::LeanObject,
    mut v_e_86_: *mut crate::leanh::LeanObject,
    mut v_s_87_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_88_ = l_Lean_FindMVar_visit(v_p_85_, v_e_86_, v_s_87_);
    crate::leanh::lean_dec(v_s_87_);
    return v_res_88_;
}
pub unsafe fn l_Lean_FindMVar_main___boxed(
    mut v_p_89_: *mut crate::leanh::LeanObject,
    mut v_x_90_: *mut crate::leanh::LeanObject,
    mut v_a_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l_Lean_FindMVar_main(v_p_89_, v_x_90_, v_a_91_);
    crate::leanh::lean_dec(v_a_91_);
    return v_res_92_;
}
pub unsafe fn l_Lean_Expr_findMVar_x3f(
    mut v_e_93_: *mut crate::leanh::LeanObject,
    mut v_p_94_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_95_ = crate::leanh::lean_box(0);
    v___x_96_ = l_Lean_FindMVar_main(v_p_94_, v_e_93_, v___x_95_);
    return v___x_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FindMVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FindMVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FindMVar(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindMVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FindMVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FindMVar(builtin);
}
