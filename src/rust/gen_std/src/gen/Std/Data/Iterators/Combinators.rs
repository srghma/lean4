// Lean compiler output
// Module: Std.Data.Iterators.Combinators
// Imports: Std.Data.Iterators.Combinators.Monadic Std.Data.Iterators.Combinators.TakeWhile Std.Data.Iterators.Combinators.Drop Std.Data.Iterators.Combinators.DropWhile Std.Data.Iterators.Combinators.StepSize Std.Data.Iterators.Combinators.Zip
use crate::r#gen::Std::Data::Iterators::Combinators::Drop::{
    initialize_Std_Data_Iterators_Combinators_Drop,
    runtime_initialize_Std_Data_Iterators_Combinators_Drop,
};
use crate::r#gen::Std::Data::Iterators::Combinators::DropWhile::{
    initialize_Std_Data_Iterators_Combinators_DropWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_DropWhile,
};
use crate::r#gen::Std::Data::Iterators::Combinators::Monadic::{
    initialize_Std_Data_Iterators_Combinators_Monadic,
    runtime_initialize_Std_Data_Iterators_Combinators_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Combinators::StepSize::{
    initialize_Std_Data_Iterators_Combinators_StepSize,
    runtime_initialize_Std_Data_Iterators_Combinators_StepSize,
};
use crate::r#gen::Std::Data::Iterators::Combinators::TakeWhile::{
    initialize_Std_Data_Iterators_Combinators_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Combinators::Zip::{
    initialize_Std_Data_Iterators_Combinators_Zip,
    runtime_initialize_Std_Data_Iterators_Combinators_Zip,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Combinators(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Combinators(
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
pub unsafe fn initialize_Std_Data_Iterators_Combinators(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Combinators_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_TakeWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_Drop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_DropWhile(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Combinators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Combinators(builtin);
}