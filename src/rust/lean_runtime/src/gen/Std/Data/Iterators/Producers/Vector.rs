// Lean compiler output
// Module: Std.Data.Iterators.Producers.Vector
// Imports: Init.Data.Vector.Basic Std.Data.Iterators.Producers.Array
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Std::Data::Iterators::Producers::Array::{
    initialize_Std_Data_Iterators_Producers_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Array,
};
pub unsafe fn l_Vector_iterFromIdx___redArg(
    mut v_xs_26_: *mut crate::leanh::LeanObject,
    mut v_pos_27_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_28_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_28_, 0, v_xs_26_);
    crate::leanh::lean_ctor_set(v___x_28_, 1, v_pos_27_);
    return v___x_28_;
}
pub unsafe fn l_Vector_iterFromIdx(
    mut v_n_29_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_30_: *mut crate::leanh::LeanObject,
    mut v_xs_31_: *mut crate::leanh::LeanObject,
    mut v_pos_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_33_, 0, v_xs_31_);
    crate::leanh::lean_ctor_set(v___x_33_, 1, v_pos_32_);
    return v___x_33_;
}
pub unsafe fn l_Vector_iterFromIdx___boxed(
    mut v_n_34_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_35_: *mut crate::leanh::LeanObject,
    mut v_xs_36_: *mut crate::leanh::LeanObject,
    mut v_pos_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_38_ = l_Vector_iterFromIdx(v_n_34_, v_00_u03b1_35_, v_xs_36_, v_pos_37_);
    crate::leanh::lean_dec(v_n_34_);
    return v_res_38_;
}
pub unsafe fn l_Vector_iter___redArg(
    mut v_xs_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_40_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_41_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_41_, 0, v_xs_39_);
    crate::leanh::lean_ctor_set(v___x_41_, 1, v___x_40_);
    return v___x_41_;
}
pub unsafe fn l_Vector_iter(
    mut v_n_42_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_43_: *mut crate::leanh::LeanObject,
    mut v_xs_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_45_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_46_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_46_, 0, v_xs_44_);
    crate::leanh::lean_ctor_set(v___x_46_, 1, v___x_45_);
    return v___x_46_;
}
pub unsafe fn l_Vector_iter___boxed(
    mut v_n_47_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_48_: *mut crate::leanh::LeanObject,
    mut v_xs_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Vector_iter(v_n_47_, v_00_u03b1_48_, v_xs_49_);
    crate::leanh::lean_dec(v_n_47_);
    return v_res_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Vector(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Vector(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Vector(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Vector(builtin);
}
