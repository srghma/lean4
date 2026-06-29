// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Total
// Imports: Init.Data.Iterators.Basic
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
pub unsafe fn l_Std_Iter_ensureTermination___redArg(
    mut v_it_11_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_11_);
    return v_it_11_;
}
pub unsafe fn l_Std_Iter_ensureTermination___redArg___boxed(
    mut v_it_12_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_13_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_13_ = l_Std_Iter_ensureTermination___redArg(v_it_12_);
    crate::leanh::lean_dec(v_it_12_);
    return v_res_13_;
}
pub unsafe fn l_Std_Iter_ensureTermination(
    mut v_00_u03b1_14_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_15_: *mut crate::leanh::LeanObject,
    mut v_it_16_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_16_);
    return v_it_16_;
}
pub unsafe fn l_Std_Iter_ensureTermination___boxed(
    mut v_00_u03b1_17_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_18_: *mut crate::leanh::LeanObject,
    mut v_it_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_20_ = l_Std_Iter_ensureTermination(v_00_u03b1_17_, v_00_u03b2_18_, v_it_19_);
    crate::leanh::lean_dec(v_it_19_);
    return v_res_20_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Total(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Total(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Total(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Total(builtin);
}
