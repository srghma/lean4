// Lean compiler output
// Module: Std.Data.Iterators.Producers.Array
// Imports: Std.Data.Iterators.Producers.Monadic.Array
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array,
};
pub unsafe fn l_Array_iterFromIdx___redArg(
    mut v_l_15_: *mut crate::leanh::LeanObject,
    mut v_pos_16_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_17_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_17_, 0, v_l_15_);
    crate::leanh::lean_ctor_set(v___x_17_, 1, v_pos_16_);
    return v___x_17_;
}
pub unsafe fn l_Array_iterFromIdx(
    mut v_00_u03b1_18_: *mut crate::leanh::LeanObject,
    mut v_l_19_: *mut crate::leanh::LeanObject,
    mut v_pos_20_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_21_, 0, v_l_19_);
    crate::leanh::lean_ctor_set(v___x_21_, 1, v_pos_20_);
    return v___x_21_;
}
pub unsafe fn l_Array_iter___redArg(
    mut v_l_22_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_23_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_24_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_24_, 0, v_l_22_);
    crate::leanh::lean_ctor_set(v___x_24_, 1, v___x_23_);
    return v___x_24_;
}
pub unsafe fn l_Array_iter(
    mut v_00_u03b1_25_: *mut crate::leanh::LeanObject,
    mut v_l_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_27_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_28_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_28_, 0, v_l_26_);
    crate::leanh::lean_ctor_set(v___x_28_, 1, v___x_27_);
    return v___x_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Array(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Array(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Array(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Array(builtin);
}
