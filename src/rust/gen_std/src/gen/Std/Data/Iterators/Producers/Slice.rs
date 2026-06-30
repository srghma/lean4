// Lean compiler output
// Module: Std.Data.Iterators.Producers.Slice
// Imports: Init.Data.Slice.Operations
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
pub unsafe fn l_Std_Slice_iter___redArg(
    mut v_inst_10_: *mut leanh::LeanObject,
    mut v_s_11_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12_ = leanh::lean_apply_1(v_inst_10_, v_s_11_);
    return v___x_12_;
}
pub unsafe fn l_Std_Slice_iter(
    mut v_00_u03b3_13_: *mut leanh::LeanObject,
    mut v_00_u03b1_14_: *mut leanh::LeanObject,
    mut v_00_u03b2_15_: *mut leanh::LeanObject,
    mut v_inst_16_: *mut leanh::LeanObject,
    mut v_s_17_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18_ = leanh::lean_apply_1(v_inst_16_, v_s_17_);
    return v___x_18_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Slice(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Slice(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Slice(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Slice(builtin);
}