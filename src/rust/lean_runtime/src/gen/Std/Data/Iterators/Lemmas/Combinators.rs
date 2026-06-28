// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators
// Imports: Std.Data.Iterators.Lemmas.Combinators.Monadic Std.Data.Iterators.Lemmas.Combinators.TakeWhile Std.Data.Iterators.Lemmas.Combinators.Drop Std.Data.Iterators.Lemmas.Combinators.DropWhile Std.Data.Iterators.Lemmas.Combinators.Zip
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Drop::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Drop,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::DropWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Monadic::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::TakeWhile::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Combinators::Zip::{
    initialize_Std_Data_Iterators_Lemmas_Combinators_Zip,
    runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Combinators(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Combinators(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Combinators(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Combinators(builtin);
}
