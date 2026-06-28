// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic
// Imports: Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::Drop::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::DropWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::FilterMap::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::TakeWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::Zip::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
}
