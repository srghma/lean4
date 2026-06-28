// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.RatAddSound
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Implementation::{
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::RatAddSound::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec_ref, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instFormulaPosFinDefaultClause(
    mut v_n_9_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_13_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_14_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_15_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_16_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_n_9_, 5);
    v___x_10_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_10_, 0, v_n_9_);
    v___x_11_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_11_, 0, v_n_9_);
    v___x_12_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_12_, 0, v_n_9_);
    v___x_13_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_13_, 0, v_n_9_);
    v___x_14_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___x_14_, 0, v_n_9_);
    v___x_15_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_15_, 0, v_n_9_);
    v___x_16_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_16_, 0, v___x_10_);
    lean_ctor_set(v___x_16_, 1, v___x_11_);
    lean_ctor_set(v___x_16_, 2, v___x_12_);
    lean_ctor_set(v___x_16_, 3, v___x_13_);
    lean_ctor_set(v___x_16_, 4, v___x_14_);
    lean_ctor_set(v___x_16_, 5, v___x_15_);
    return v___x_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RatAddSound(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
}
