// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Drop
// Imports: Std.Data.Iterators.Combinators.Monadic.Drop
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::Drop::{
    initialize_Std_Data_Iterators_Combinators_Monadic_Drop,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Iter_drop___redArg(
    mut v_n_9_: *mut LeanObject,
    mut v_it_10_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11_: *mut LeanObject = core::ptr::null_mut();
    v___x_11_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_11_, 0, v_n_9_);
    lean_ctor_set(v___x_11_, 1, v_it_10_);
    return v___x_11_;
}
pub unsafe fn l_Std_Iter_drop(
    mut v_00_u03b1_12_: *mut LeanObject,
    mut v_00_u03b2_13_: *mut LeanObject,
    mut v_n_14_: *mut LeanObject,
    mut v_it_15_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_16_: *mut LeanObject = core::ptr::null_mut();
    v___x_16_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_16_, 0, v_n_14_);
    lean_ctor_set(v___x_16_, 1, v_it_15_);
    return v___x_16_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators_Drop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators_Drop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Combinators_Drop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators_Drop(builtin);
}
