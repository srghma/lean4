// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Append
// Imports: Init.Data.Iterators.Combinators.Monadic.Append
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Append::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Append,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Iter_append___redArg(
    mut v_it_u2081_34_: *mut LeanObject,
    mut v_it_u2082_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_36_, 0, v_it_u2081_34_);
    lean_ctor_set(v___x_36_, 1, v_it_u2082_35_);
    return v___x_36_;
}
pub unsafe fn l_Std_Iter_append(
    mut v_00_u03b1_u2081_37_: *mut LeanObject,
    mut v_00_u03b1_u2082_38_: *mut LeanObject,
    mut v_00_u03b2_39_: *mut LeanObject,
    mut v_inst_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
    mut v_it_u2081_42_: *mut LeanObject,
    mut v_it_u2082_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_44_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_44_, 0, v_it_u2081_42_);
    lean_ctor_set(v___x_44_, 1, v_it_u2082_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_Iter_append___boxed(
    mut v_00_u03b1_u2081_45_: *mut LeanObject,
    mut v_00_u03b1_u2082_46_: *mut LeanObject,
    mut v_00_u03b2_47_: *mut LeanObject,
    mut v_inst_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
    mut v_it_u2081_50_: *mut LeanObject,
    mut v_it_u2082_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_52_: *mut LeanObject = core::ptr::null_mut();
    v_res_52_ = l_Std_Iter_append(
        v_00_u03b1_u2081_45_,
        v_00_u03b1_u2082_46_,
        v_00_u03b2_47_,
        v_inst_48_,
        v_inst_49_,
        v_it_u2081_50_,
        v_it_u2082_51_,
    );
    lean_dec(v_inst_49_);
    lean_dec(v_inst_48_);
    return v_res_52_;
}
pub unsafe fn l_Std_Iter_Intermediate_appendSnd___redArg(
    mut v_it_u2082_53_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    v___x_54_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_54_, 0, v_it_u2082_53_);
    return v___x_54_;
}
pub unsafe fn l_Std_Iter_Intermediate_appendSnd(
    mut v_00_u03b1_u2082_55_: *mut LeanObject,
    mut v_00_u03b2_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
    mut v_00_u03b1_u2081_58_: *mut LeanObject,
    mut v_it_u2082_59_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    v___x_60_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_60_, 0, v_it_u2082_59_);
    return v___x_60_;
}
pub unsafe fn l_Std_Iter_Intermediate_appendSnd___boxed(
    mut v_00_u03b1_u2082_61_: *mut LeanObject,
    mut v_00_u03b2_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
    mut v_00_u03b1_u2081_64_: *mut LeanObject,
    mut v_it_u2082_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Std_Iter_Intermediate_appendSnd(
        v_00_u03b1_u2082_61_,
        v_00_u03b2_62_,
        v_inst_63_,
        v_00_u03b1_u2081_64_,
        v_it_u2082_65_,
    );
    lean_dec(v_inst_63_);
    return v_res_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Append(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Append(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Append(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Append(builtin);
}
