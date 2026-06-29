// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadVar
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0(
    mut v_inst_27_: *mut crate::leanh::LeanObject,
    mut v_inst_28_: *mut crate::leanh::LeanObject,
    mut v_x_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = crate::leanh::lean_apply_1(v_inst_27_, v_x_29_);
    v___x_31_ = crate::leanh::lean_apply_2(v_inst_28_, crate::leanh::lean_box(0), v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg(
    mut v_inst_32_: *mut crate::leanh::LeanObject,
    mut v_inst_33_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_34_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_34_, 0, v_inst_33_);
    crate::leanh::lean_closure_set(v___f_34_, 1, v_inst_32_);
    return v___f_34_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift(
    mut v_m_35_: *mut crate::leanh::LeanObject,
    mut v_n_36_: *mut crate::leanh::LeanObject,
    mut v_inst_37_: *mut crate::leanh::LeanObject,
    mut v_inst_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_39_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_39_, 0, v_inst_38_);
    crate::leanh::lean_closure_set(v___f_39_, 1, v_inst_37_);
    return v___f_39_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0(
    mut v_inst_40_: *mut crate::leanh::LeanObject,
    mut v_inst_41_: *mut crate::leanh::LeanObject,
    mut v_e_42_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_43_ = crate::leanh::lean_apply_1(v_inst_40_, v_e_42_);
    v___x_44_ = crate::leanh::lean_apply_2(v_inst_41_, crate::leanh::lean_box(0), v___x_43_);
    return v___x_44_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg(
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_47_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_47_, 0, v_inst_46_);
    crate::leanh::lean_closure_set(v___f_47_, 1, v_inst_45_);
    return v___f_47_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift(
    mut v_m_48_: *mut crate::leanh::LeanObject,
    mut v_n_49_: *mut crate::leanh::LeanObject,
    mut v_inst_50_: *mut crate::leanh::LeanObject,
    mut v_inst_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_52_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_52_, 0, v_inst_51_);
    crate::leanh::lean_closure_set(v___f_52_, 1, v_inst_50_);
    return v___f_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadVar(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
}
