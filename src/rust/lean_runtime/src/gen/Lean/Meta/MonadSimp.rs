// Lean compiler output
// Module: Lean.Meta.MonadSimp
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
pub static mut l_Lean_Meta_MonadSimp_instInhabitedResult_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_MonadSimp_instInhabitedResult: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorIdx(
    mut v_x_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_41_) == 0 {
        let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_42_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_42_;
    } else {
        let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_43_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_43_;
    }
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorIdx___boxed(
    mut v_x_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_45_ = l_Lean_Meta_MonadSimp_Result_ctorIdx(v_x_44_);
    crate::leanh::lean_dec(v_x_44_);
    return v_res_45_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(
    mut v_t_46_: *mut crate::leanh::LeanObject,
    mut v_k_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_46_) == 0 {
        return v_k_47_;
    } else {
        let mut v_e_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_h_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_48_ = crate::leanh::lean_ctor_get(v_t_46_, 0);
        crate::leanh::lean_inc_ref(v_e_48_);
        v_h_49_ = crate::leanh::lean_ctor_get(v_t_46_, 1);
        crate::leanh::lean_inc_ref(v_h_49_);
        crate::leanh::lean_dec_ref_known(v_t_46_, 2);
        v___x_50_ = crate::leanh::lean_apply_2(v_k_47_, v_e_48_, v_h_49_);
        return v___x_50_;
    }
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim(
    mut v_motive_51_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_52_: *mut crate::leanh::LeanObject,
    mut v_t_53_: *mut crate::leanh::LeanObject,
    mut v_h_54_: *mut crate::leanh::LeanObject,
    mut v_k_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_56_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_53_, v_k_55_);
    return v___x_56_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(
    mut v_motive_57_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_58_: *mut crate::leanh::LeanObject,
    mut v_t_59_: *mut crate::leanh::LeanObject,
    mut v_h_60_: *mut crate::leanh::LeanObject,
    mut v_k_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Lean_Meta_MonadSimp_Result_ctorElim(
        v_motive_57_,
        v_ctorIdx_58_,
        v_t_59_,
        v_h_60_,
        v_k_61_,
    );
    crate::leanh::lean_dec(v_ctorIdx_58_);
    return v_res_62_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(
    mut v_t_63_: *mut crate::leanh::LeanObject,
    mut v_rfl_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_65_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_63_, v_rfl_64_);
    return v___x_65_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_rfl_elim(
    mut v_motive_66_: *mut crate::leanh::LeanObject,
    mut v_t_67_: *mut crate::leanh::LeanObject,
    mut v_h_68_: *mut crate::leanh::LeanObject,
    mut v_rfl_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_70_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_67_, v_rfl_69_);
    return v___x_70_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_step_elim___redArg(
    mut v_t_71_: *mut crate::leanh::LeanObject,
    mut v_step_72_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_73_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_71_, v_step_72_);
    return v___x_73_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_step_elim(
    mut v_motive_74_: *mut crate::leanh::LeanObject,
    mut v_t_75_: *mut crate::leanh::LeanObject,
    mut v_h_76_: *mut crate::leanh::LeanObject,
    mut v_step_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_78_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_75_, v_step_77_);
    return v___x_78_;
}
pub unsafe fn _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = crate::leanh::lean_box(0);
    return v___x_79_;
}
pub unsafe fn _init_l_Lean_Meta_MonadSimp_instInhabitedResult() -> *mut crate::leanh::LeanObject {
    let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_80_ = crate::leanh::lean_box(0);
    return v___x_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    l_Lean_Meta_MonadSimp_instInhabitedResult_default =
        _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult_default);
    l_Lean_Meta_MonadSimp_instInhabitedResult = _init_l_Lean_Meta_MonadSimp_instInhabitedResult();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MonadSimp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_MonadSimp(builtin);
}
