// Lean compiler output
// Module: Std.Data.Iterators.Producers.Slice
// Imports: Init.Data.Slice.Operations
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
pub unsafe fn l_Std_Slice_iter___redArg(
    mut v_inst_10_: *mut crate::leanh::LeanObject,
    mut v_s_11_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12_ = crate::leanh::lean_apply_1(v_inst_10_, v_s_11_);
    return v___x_12_;
}
pub unsafe fn l_Std_Slice_iter(
    mut v_00_u03b3_13_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_14_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_15_: *mut crate::leanh::LeanObject,
    mut v_inst_16_: *mut crate::leanh::LeanObject,
    mut v_s_17_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18_ = crate::leanh::lean_apply_1(v_inst_16_, v_s_17_);
    return v___x_18_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Slice(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Slice(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Slice(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Slice(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Slice(builtin);
}
