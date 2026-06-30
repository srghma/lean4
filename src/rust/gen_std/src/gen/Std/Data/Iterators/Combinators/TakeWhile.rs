// Lean compiler output
// Module: Std.Data.Iterators.Combinators.TakeWhile
// Imports: Std.Data.Iterators.Combinators.Monadic.TakeWhile
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::TakeWhile::{
    initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile,
};
pub unsafe fn l_Std_Iter_takeWhile___redArg(
    mut v_it_13_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_13_);
    return v_it_13_;
}
pub unsafe fn l_Std_Iter_takeWhile___redArg___boxed(
    mut v_it_14_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_15_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_15_ = l_Std_Iter_takeWhile___redArg(v_it_14_);
    leanh::lean_dec(v_it_14_);
    return v_res_15_;
}
pub unsafe fn l_Std_Iter_takeWhile(
    mut v_00_u03b1_16_: *mut leanh::LeanObject,
    mut v_00_u03b2_17_: *mut leanh::LeanObject,
    mut v_P_18_: *mut leanh::LeanObject,
    mut v_it_19_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_it_19_);
    return v_it_19_;
}
pub unsafe fn l_Std_Iter_takeWhile___boxed(
    mut v_00_u03b1_20_: *mut leanh::LeanObject,
    mut v_00_u03b2_21_: *mut leanh::LeanObject,
    mut v_P_22_: *mut leanh::LeanObject,
    mut v_it_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_24_ = l_Std_Iter_takeWhile(v_00_u03b1_20_, v_00_u03b2_21_, v_P_22_, v_it_23_);
    leanh::lean_dec(v_it_23_);
    leanh::lean_dec_ref(v_P_22_);
    return v_res_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_TakeWhile(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_TakeWhile(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
}