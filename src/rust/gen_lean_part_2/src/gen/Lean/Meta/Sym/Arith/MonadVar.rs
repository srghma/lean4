// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadVar
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0(
    mut v_inst_27_: *mut leanh::LeanObject,
    mut v_inst_28_: *mut leanh::LeanObject,
    mut v_x_29_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = leanh::lean_apply_1(v_inst_27_, v_x_29_);
    v___x_31_ = leanh::lean_apply_2(v_inst_28_, leanh::lean_box(0), v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg(
    mut v_inst_32_: *mut leanh::LeanObject,
    mut v_inst_33_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_34_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_34_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_34_, 0, v_inst_33_);
    leanh::lean_closure_set(v___f_34_, 1, v_inst_32_);
    return v___f_34_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift(
    mut v_m_35_: *mut leanh::LeanObject,
    mut v_n_36_: *mut leanh::LeanObject,
    mut v_inst_37_: *mut leanh::LeanObject,
    mut v_inst_38_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_39_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_39_, 0, v_inst_38_);
    leanh::lean_closure_set(v___f_39_, 1, v_inst_37_);
    return v___f_39_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0(
    mut v_inst_40_: *mut leanh::LeanObject,
    mut v_inst_41_: *mut leanh::LeanObject,
    mut v_e_42_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_43_ = leanh::lean_apply_1(v_inst_40_, v_e_42_);
    v___x_44_ = leanh::lean_apply_2(v_inst_41_, leanh::lean_box(0), v___x_43_);
    return v___x_44_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg(
    mut v_inst_45_: *mut leanh::LeanObject,
    mut v_inst_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_47_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_47_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_47_, 0, v_inst_46_);
    leanh::lean_closure_set(v___f_47_, 1, v_inst_45_);
    return v___f_47_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift(
    mut v_m_48_: *mut leanh::LeanObject,
    mut v_n_49_: *mut leanh::LeanObject,
    mut v_inst_50_: *mut leanh::LeanObject,
    mut v_inst_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_52_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_52_, 0, v_inst_51_);
    leanh::lean_closure_set(v___f_52_, 1, v_inst_50_);
    return v___f_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadVar(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadVar(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
}