// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Drop
// Imports: Std.Data.Iterators.Combinators.Monadic.Drop
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::Drop::{
    initialize_Std_Data_Iterators_Combinators_Monadic_Drop,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop,
};
pub unsafe fn l_Std_Iter_drop___redArg(
    mut v_n_9_: *mut leanh::LeanObject,
    mut v_it_10_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_11_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_11_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_11_, 0, v_n_9_);
    leanh::lean_ctor_set(v___x_11_, 1, v_it_10_);
    return v___x_11_;
}
pub unsafe fn l_Std_Iter_drop(
    mut v_00_u03b1_12_: *mut leanh::LeanObject,
    mut v_00_u03b2_13_: *mut leanh::LeanObject,
    mut v_n_14_: *mut leanh::LeanObject,
    mut v_it_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_16_, 0, v_n_14_);
    leanh::lean_ctor_set(v___x_16_, 1, v_it_15_);
    return v___x_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Drop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Drop(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Drop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Drop(builtin);
}