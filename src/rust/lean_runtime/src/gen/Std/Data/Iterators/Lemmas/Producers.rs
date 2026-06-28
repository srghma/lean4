// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers
// Imports: Std.Data.Iterators.Lemmas.Producers.Monadic Std.Data.Iterators.Lemmas.Producers.Array Std.Data.Iterators.Lemmas.Producers.Vector Std.Data.Iterators.Lemmas.Producers.Empty Std.Data.Iterators.Lemmas.Producers.Repeat Std.Data.Iterators.Lemmas.Producers.Range Std.Data.Iterators.Lemmas.Producers.Slice
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Array::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Array,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Empty::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Empty,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Empty,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Range::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Range,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Range,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Repeat::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Repeat,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Slice::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Slice,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Vector::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Vector,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Vector,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers(builtin);
}
