// Lean compiler output
// Module: Std.Data.Iterators.Producers.Array
// Imports: Std.Data.Iterators.Producers.Monadic.Array
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Array_iterFromIdx___redArg(
    mut v_l_15_: *mut LeanObject,
    mut v_pos_16_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_17_: *mut LeanObject = core::ptr::null_mut();
    v___x_17_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_17_, 0, v_l_15_);
    lean_ctor_set(v___x_17_, 1, v_pos_16_);
    return v___x_17_;
}
pub unsafe fn l_Array_iterFromIdx(
    mut v_00_u03b1_18_: *mut LeanObject,
    mut v_l_19_: *mut LeanObject,
    mut v_pos_20_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_21_: *mut LeanObject = core::ptr::null_mut();
    v___x_21_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_21_, 0, v_l_19_);
    lean_ctor_set(v___x_21_, 1, v_pos_20_);
    return v___x_21_;
}
pub unsafe fn l_Array_iter___redArg(mut v_l_22_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    v___x_23_ = lean_unsigned_to_nat(0);
    v___x_24_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_24_, 0, v_l_22_);
    lean_ctor_set(v___x_24_, 1, v___x_23_);
    return v___x_24_;
}
pub unsafe fn l_Array_iter(
    mut v_00_u03b1_25_: *mut LeanObject,
    mut v_l_26_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
    v___x_27_ = lean_unsigned_to_nat(0);
    v___x_28_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_28_, 0, v_l_26_);
    lean_ctor_set(v___x_28_, 1, v___x_27_);
    return v___x_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Array(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Producers_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Array(builtin);
}
