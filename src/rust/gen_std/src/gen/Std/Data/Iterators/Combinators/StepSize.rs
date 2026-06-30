// Lean compiler output
// Module: Std.Data.Iterators.Combinators.StepSize
// Imports: Std.Data.Iterators.Combinators.Monadic.StepSize
use crate::ffi::lean_nat_sub;
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::StepSize::{
    initialize_Std_Data_Iterators_Combinators_Monadic_StepSize,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize,
};
pub unsafe fn l_Std_Iter_stepSize___redArg(
    mut v_it_27_: *mut leanh::LeanObject,
    mut v_n_28_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_29_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_29_ = leanh::lean_unsigned_to_nat(0);
    v___x_30_ = leanh::lean_unsigned_to_nat(1);
    v___x_31_ = lean_nat_sub(v_n_28_, v___x_30_);
    v___x_32_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_32_, 0, v___x_29_);
    leanh::lean_ctor_set(v___x_32_, 1, v___x_31_);
    leanh::lean_ctor_set(v___x_32_, 2, v_it_27_);
    return v___x_32_;
}
pub unsafe fn l_Std_Iter_stepSize___redArg___boxed(
    mut v_it_33_: *mut leanh::LeanObject,
    mut v_n_34_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_35_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_35_ = l_Std_Iter_stepSize___redArg(v_it_33_, v_n_34_);
    leanh::lean_dec(v_n_34_);
    return v_res_35_;
}
pub unsafe fn l_Std_Iter_stepSize(
    mut v_00_u03b1_36_: *mut leanh::LeanObject,
    mut v_00_u03b2_37_: *mut leanh::LeanObject,
    mut v_inst_38_: *mut leanh::LeanObject,
    mut v_inst_39_: *mut leanh::LeanObject,
    mut v_it_40_: *mut leanh::LeanObject,
    mut v_n_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_42_ = leanh::lean_unsigned_to_nat(0);
    v___x_43_ = leanh::lean_unsigned_to_nat(1);
    v___x_44_ = lean_nat_sub(v_n_41_, v___x_43_);
    v___x_45_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_45_, 0, v___x_42_);
    leanh::lean_ctor_set(v___x_45_, 1, v___x_44_);
    leanh::lean_ctor_set(v___x_45_, 2, v_it_40_);
    return v___x_45_;
}
pub unsafe fn l_Std_Iter_stepSize___boxed(
    mut v_00_u03b1_46_: *mut leanh::LeanObject,
    mut v_00_u03b2_47_: *mut leanh::LeanObject,
    mut v_inst_48_: *mut leanh::LeanObject,
    mut v_inst_49_: *mut leanh::LeanObject,
    mut v_it_50_: *mut leanh::LeanObject,
    mut v_n_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_52_ = l_Std_Iter_stepSize(
        v_00_u03b1_46_,
        v_00_u03b2_47_,
        v_inst_48_,
        v_inst_49_,
        v_it_50_,
        v_n_51_,
    );
    leanh::lean_dec(v_n_51_);
    leanh::lean_dec_ref(v_inst_49_);
    leanh::lean_dec(v_inst_48_);
    return v_res_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_StepSize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_StepSize(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators_StepSize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
}