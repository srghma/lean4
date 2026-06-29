// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Attach
// Imports: Init.Data.Iterators.Combinators.Monadic.Attach
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::Attach::{
    initialize_Init_Data_Iterators_Combinators_Monadic_Attach,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach,
};
pub unsafe fn l_Std_Iter_attachWith___redArg(
    mut v_it_17_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_17_);
    return v_it_17_;
}
pub unsafe fn l_Std_Iter_attachWith___redArg___boxed(
    mut v_it_18_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_19_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_19_ = l_Std_Iter_attachWith___redArg(v_it_18_);
    crate::leanh::lean_dec(v_it_18_);
    return v_res_19_;
}
pub unsafe fn l_Std_Iter_attachWith(
    mut v_00_u03b1_20_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_21_: *mut crate::leanh::LeanObject,
    mut v_inst_22_: *mut crate::leanh::LeanObject,
    mut v_it_23_: *mut crate::leanh::LeanObject,
    mut v_P_24_: *mut crate::leanh::LeanObject,
    mut v_h_25_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_it_23_);
    return v_it_23_;
}
pub unsafe fn l_Std_Iter_attachWith___boxed(
    mut v_00_u03b1_26_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_27_: *mut crate::leanh::LeanObject,
    mut v_inst_28_: *mut crate::leanh::LeanObject,
    mut v_it_29_: *mut crate::leanh::LeanObject,
    mut v_P_30_: *mut crate::leanh::LeanObject,
    mut v_h_31_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_32_ = l_Std_Iter_attachWith(
        v_00_u03b1_26_,
        v_00_u03b2_27_,
        v_inst_28_,
        v_it_29_,
        v_P_30_,
        v_h_31_,
    );
    crate::leanh::lean_dec(v_it_29_);
    crate::leanh::lean_dec(v_inst_28_);
    return v_res_32_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_Attach(
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
pub unsafe fn initialize_Init_Data_Iterators_Combinators_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_Attach(builtin);
}
