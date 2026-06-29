// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic
// Imports: Std.Data.Iterators.Lemmas.Producers.Monadic.Array Std.Data.Iterators.Lemmas.Producers.Monadic.Vector Std.Data.Iterators.Lemmas.Producers.Monadic.Empty Std.Data.Iterators.Lemmas.Producers.Monadic.List
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::Empty::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::List::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Producers::Monadic::Vector::{
    initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector,
    runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(builtin);
}
