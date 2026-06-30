// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Repeat
// Imports: Std.Data.Iterators.Producers.Repeat Init.Data.Iterators.Lemmas.Combinators.Take Init.Data.Iterators.Lemmas.Consumers.Access Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::Take::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Access::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Std::Data::Iterators::Producers::Repeat::{
    initialize_Std_Data_Iterators_Producers_Repeat,
    runtime_initialize_Std_Data_Iterators_Producers_Repeat,
};
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter___redArg(
    mut v_x_35_: *mut leanh::LeanObject,
    mut v_x_36_: *mut leanh::LeanObject,
    mut v_h__1_37_: *mut leanh::LeanObject,
    mut v_h__2_38_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_40_: u8 = 0;
    v_zero_39_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_40_ = lean_nat_dec_eq(v_x_35_, v_zero_39_);
    if v_isZero_40_ == 1 {
        let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_38_);
        v___x_41_ = leanh::lean_apply_1(v_h__1_37_, v_x_36_);
        return v___x_41_;
    } else {
        let mut v_one_42_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_43_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_37_);
        v_one_42_ = leanh::lean_unsigned_to_nat(1);
        v_n_43_ = lean_nat_sub(v_x_35_, v_one_42_);
        v___x_44_ = leanh::lean_apply_2(v_h__2_38_, v_n_43_, v_x_36_);
        return v___x_44_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter___redArg___boxed(
    mut v_x_45_: *mut leanh::LeanObject,
    mut v_x_46_: *mut leanh::LeanObject,
    mut v_h__1_47_: *mut leanh::LeanObject,
    mut v_h__2_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_49_ = l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter___redArg(v_x_45_, v_x_46_, v_h__1_47_, v_h__2_48_);
    leanh::lean_dec(v_x_45_);
    return v_res_49_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter(
    mut v_00_u03b1_50_: *mut leanh::LeanObject,
    mut v_motive_51_: *mut leanh::LeanObject,
    mut v_x_52_: *mut leanh::LeanObject,
    mut v_x_53_: *mut leanh::LeanObject,
    mut v_h__1_54_: *mut leanh::LeanObject,
    mut v_h__2_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_57_: u8 = 0;
    v_zero_56_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_57_ = lean_nat_dec_eq(v_x_52_, v_zero_56_);
    if v_isZero_57_ == 1 {
        let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_55_);
        v___x_58_ = leanh::lean_apply_1(v_h__1_54_, v_x_53_);
        return v___x_58_;
    } else {
        let mut v_one_59_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_60_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_54_);
        v_one_59_ = leanh::lean_unsigned_to_nat(1);
        v_n_60_ = lean_nat_sub(v_x_52_, v_one_59_);
        v___x_61_ = leanh::lean_apply_2(v_h__2_55_, v_n_60_, v_x_53_);
        return v___x_61_;
    }
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter___boxed(
    mut v_00_u03b1_62_: *mut leanh::LeanObject,
    mut v_motive_63_: *mut leanh::LeanObject,
    mut v_x_64_: *mut leanh::LeanObject,
    mut v_x_65_: *mut leanh::LeanObject,
    mut v_h__1_66_: *mut leanh::LeanObject,
    mut v_h__2_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_68_ =
        l___private_Std_Data_Iterators_Lemmas_Producers_Repeat_0__Nat_repeat_match__1_splitter(
            v_00_u03b1_62_,
            v_motive_63_,
            v_x_64_,
            v_x_65_,
            v_h__1_66_,
            v_h__2_67_,
        );
    leanh::lean_dec(v_x_64_);
    return v_res_68_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin);
}