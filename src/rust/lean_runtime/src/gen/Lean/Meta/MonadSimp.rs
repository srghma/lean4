// Lean compiler output
// Module: Lean.Meta.MonadSimp
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_MonadSimp_instInhabitedResult_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_MonadSimp_instInhabitedResult: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorIdx(
    mut v_x_41_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_41_) == 0 {
        let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
        v___x_42_ = lean_unsigned_to_nat(0);
        return v___x_42_;
    } else {
        let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
        v___x_43_ = lean_unsigned_to_nat(1);
        return v___x_43_;
    }
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorIdx___boxed(
    mut v_x_44_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_45_: *mut LeanObject = core::ptr::null_mut();
    v_res_45_ = l_Lean_Meta_MonadSimp_Result_ctorIdx(v_x_44_);
    lean_dec(v_x_44_);
    return v_res_45_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(
    mut v_t_46_: *mut LeanObject,
    mut v_k_47_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_46_) == 0 {
        return v_k_47_;
    } else {
        let mut v_e_48_: *mut LeanObject = core::ptr::null_mut();
        let mut v_h_49_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
        v_e_48_ = lean_ctor_get(v_t_46_, 0);
        lean_inc_ref(v_e_48_);
        v_h_49_ = lean_ctor_get(v_t_46_, 1);
        lean_inc_ref(v_h_49_);
        lean_dec_ref_known(v_t_46_, 2);
        v___x_50_ = lean_apply_2(v_k_47_, v_e_48_, v_h_49_);
        return v___x_50_;
    }
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim(
    mut v_motive_51_: *mut LeanObject,
    mut v_ctorIdx_52_: *mut LeanObject,
    mut v_t_53_: *mut LeanObject,
    mut v_h_54_: *mut LeanObject,
    mut v_k_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
    v___x_56_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_53_, v_k_55_);
    return v___x_56_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_ctorElim___boxed(
    mut v_motive_57_: *mut LeanObject,
    mut v_ctorIdx_58_: *mut LeanObject,
    mut v_t_59_: *mut LeanObject,
    mut v_h_60_: *mut LeanObject,
    mut v_k_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_62_: *mut LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Lean_Meta_MonadSimp_Result_ctorElim(
        v_motive_57_,
        v_ctorIdx_58_,
        v_t_59_,
        v_h_60_,
        v_k_61_,
    );
    lean_dec(v_ctorIdx_58_);
    return v_res_62_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_rfl_elim___redArg(
    mut v_t_63_: *mut LeanObject,
    mut v_rfl_64_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_65_: *mut LeanObject = core::ptr::null_mut();
    v___x_65_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_63_, v_rfl_64_);
    return v___x_65_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_rfl_elim(
    mut v_motive_66_: *mut LeanObject,
    mut v_t_67_: *mut LeanObject,
    mut v_h_68_: *mut LeanObject,
    mut v_rfl_69_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    v___x_70_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_67_, v_rfl_69_);
    return v___x_70_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_step_elim___redArg(
    mut v_t_71_: *mut LeanObject,
    mut v_step_72_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
    v___x_73_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_71_, v_step_72_);
    return v___x_73_;
}
pub unsafe fn l_Lean_Meta_MonadSimp_Result_step_elim(
    mut v_motive_74_: *mut LeanObject,
    mut v_t_75_: *mut LeanObject,
    mut v_h_76_: *mut LeanObject,
    mut v_step_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    v___x_78_ = l_Lean_Meta_MonadSimp_Result_ctorElim___redArg(v_t_75_, v_step_77_);
    return v___x_78_;
}
pub unsafe fn _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default() -> *mut LeanObject {
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v___x_79_ = lean_box(0);
    return v___x_79_;
}
pub unsafe fn _init_l_Lean_Meta_MonadSimp_instInhabitedResult() -> *mut LeanObject {
    let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
    v___x_80_ = lean_box(0);
    return v___x_80_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_MonadSimp_instInhabitedResult_default =
        _init_l_Lean_Meta_MonadSimp_instInhabitedResult_default();
    lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult_default);
    l_Lean_Meta_MonadSimp_instInhabitedResult = _init_l_Lean_Meta_MonadSimp_instInhabitedResult();
    lean_mark_persistent(l_Lean_Meta_MonadSimp_instInhabitedResult);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MonadSimp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MonadSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_MonadSimp(builtin);
}
