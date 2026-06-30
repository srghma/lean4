// Lean compiler output
// Module: Init.Data.Iterators.Producers.List
// Imports: Init.Data.Iterators.Producers.Monadic.List
use crate::r#gen::Init::Data::Iterators::Producers::Monadic::List::{
    initialize_Init_Data_Iterators_Producers_Monadic_List,
    runtime_initialize_Init_Data_Iterators_Producers_Monadic_List,
};
pub unsafe fn l_List_iter___redArg(
    mut v_l_9_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_9_);
    return v_l_9_;
}
pub unsafe fn l_List_iter___redArg___boxed(
    mut v_l_10_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_11_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_11_ = l_List_iter___redArg(v_l_10_);
    leanh::lean_dec(v_l_10_);
    return v_res_11_;
}
pub unsafe fn l_List_iter(
    mut v_00_u03b1_12_: *mut leanh::LeanObject,
    mut v_l_13_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_l_13_);
    return v_l_13_;
}
pub unsafe fn l_List_iter___boxed(
    mut v_00_u03b1_14_: *mut leanh::LeanObject,
    mut v_l_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_16_ = l_List_iter(v_00_u03b1_14_, v_l_15_);
    leanh::lean_dec(v_l_15_);
    return v_res_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Producers_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Producers_List(
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
pub unsafe fn initialize_Init_Data_Iterators_Producers_List(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Producers_Monadic_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Producers_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Producers_List(builtin);
}