// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Zip
// Imports: Std.Data.Iterators.Combinators.Monadic.Zip
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::Zip::{
    initialize_Std_Data_Iterators_Combinators_Monadic_Zip,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Iter_zip___redArg(
    mut v_left_24_: *mut LeanObject,
    mut v_right_25_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_26_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
    v___x_26_ = lean_box(0);
    v___x_27_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_27_, 0, v_left_24_);
    lean_ctor_set(v___x_27_, 1, v___x_26_);
    lean_ctor_set(v___x_27_, 2, v_right_25_);
    return v___x_27_;
}
pub unsafe fn l_Std_Iter_zip(
    mut v_00_u03b1_u2081_28_: *mut LeanObject,
    mut v_00_u03b2_u2081_29_: *mut LeanObject,
    mut v_00_u03b1_u2082_30_: *mut LeanObject,
    mut v_00_u03b2_u2082_31_: *mut LeanObject,
    mut v_inst_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_left_34_: *mut LeanObject,
    mut v_right_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = lean_box(0);
    v___x_37_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_37_, 0, v_left_34_);
    lean_ctor_set(v___x_37_, 1, v___x_36_);
    lean_ctor_set(v___x_37_, 2, v_right_35_);
    return v___x_37_;
}
pub unsafe fn l_Std_Iter_zip___boxed(
    mut v_00_u03b1_u2081_38_: *mut LeanObject,
    mut v_00_u03b2_u2081_39_: *mut LeanObject,
    mut v_00_u03b1_u2082_40_: *mut LeanObject,
    mut v_00_u03b2_u2082_41_: *mut LeanObject,
    mut v_inst_42_: *mut LeanObject,
    mut v_inst_43_: *mut LeanObject,
    mut v_left_44_: *mut LeanObject,
    mut v_right_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_46_: *mut LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_Iter_zip(
        v_00_u03b1_u2081_38_,
        v_00_u03b2_u2081_39_,
        v_00_u03b1_u2082_40_,
        v_00_u03b2_u2082_41_,
        v_inst_42_,
        v_inst_43_,
        v_left_44_,
        v_right_45_,
    );
    lean_dec(v_inst_43_);
    lean_dec(v_inst_42_);
    return v_res_46_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Zip(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Zip(builtin);
}
