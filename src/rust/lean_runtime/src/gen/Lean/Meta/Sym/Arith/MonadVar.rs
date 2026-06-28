// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadVar
// Imports: Lean.Meta.Sym.Arith.Types
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    initialize_Lean_Meta_Sym_Arith_Types, runtime_initialize_Lean_Meta_Sym_Arith_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_box,
    lean_closure_set, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0(
    mut v_inst_27_: *mut LeanObject,
    mut v_inst_28_: *mut LeanObject,
    mut v_x_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    v___x_30_ = lean_apply_1(v_inst_27_, v_x_29_);
    v___x_31_ = lean_apply_2(v_inst_28_, lean_box(0), v___x_30_);
    return v___x_31_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg(
    mut v_inst_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_34_: *mut LeanObject = core::ptr::null_mut();
    v___f_34_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_34_, 0, v_inst_33_);
    lean_closure_set(v___f_34_, 1, v_inst_32_);
    return v___f_34_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift(
    mut v_m_35_: *mut LeanObject,
    mut v_n_36_: *mut LeanObject,
    mut v_inst_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_39_: *mut LeanObject = core::ptr::null_mut();
    v___f_39_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadGetVarOfMonadLift___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_39_, 0, v_inst_38_);
    lean_closure_set(v___f_39_, 1, v_inst_37_);
    return v___f_39_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0(
    mut v_inst_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
    mut v_e_42_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_43_ = lean_apply_1(v_inst_40_, v_e_42_);
    v___x_44_ = lean_apply_2(v_inst_41_, lean_box(0), v___x_43_);
    return v___x_44_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg(
    mut v_inst_45_: *mut LeanObject,
    mut v_inst_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_47_: *mut LeanObject = core::ptr::null_mut();
    v___f_47_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_47_, 0, v_inst_46_);
    lean_closure_set(v___f_47_, 1, v_inst_45_);
    return v___f_47_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift(
    mut v_m_48_: *mut LeanObject,
    mut v_n_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_52_: *mut LeanObject = core::ptr::null_mut();
    v___f_52_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Arith_instMonadMkVarOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_52_, 0, v_inst_51_);
    lean_closure_set(v___f_52_, 1, v_inst_50_);
    return v___f_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_MonadVar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_MonadVar(builtin);
}
