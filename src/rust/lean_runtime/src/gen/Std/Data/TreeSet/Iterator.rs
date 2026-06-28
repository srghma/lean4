// Lean compiler output
// Module: Std.Data.TreeSet.Iterator
// Imports: Std.Data.TreeSet.Basic Std.Data.TreeMap.Iterator Std.Data.DTreeMap.Lemmas Init.Data.Iterators.Lemmas.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Zipper::l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg;
use crate::r#gen::Std::Data::DTreeMap::Lemmas::{
    initialize_Std_Data_DTreeMap_Lemmas, runtime_initialize_Std_Data_DTreeMap_Lemmas,
};
use crate::r#gen::Std::Data::TreeMap::Iterator::{
    initialize_Std_Data_TreeMap_Iterator, runtime_initialize_Std_Data_TreeMap_Iterator,
};
use crate::r#gen::Std::Data::TreeSet::Basic::{
    initialize_Std_Data_TreeSet_Basic, runtime_initialize_Std_Data_TreeSet_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_TreeSet_iter___redArg(mut v_m_13_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_14_: *mut LeanObject = core::ptr::null_mut();
    v___x_14_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_13_);
    return v___x_14_;
}
pub unsafe fn l_Std_TreeSet_iter___redArg___boxed(mut v_m_15_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_16_: *mut LeanObject = core::ptr::null_mut();
    v_res_16_ = l_Std_TreeSet_iter___redArg(v_m_15_);
    lean_dec(v_m_15_);
    return v_res_16_;
}
pub unsafe fn l_Std_TreeSet_iter(
    mut v_00_u03b1_17_: *mut LeanObject,
    mut v_cmp_18_: *mut LeanObject,
    mut v_m_19_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_20_: *mut LeanObject = core::ptr::null_mut();
    v___x_20_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_19_);
    return v___x_20_;
}
pub unsafe fn l_Std_TreeSet_iter___boxed(
    mut v_00_u03b1_21_: *mut LeanObject,
    mut v_cmp_22_: *mut LeanObject,
    mut v_m_23_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_24_: *mut LeanObject = core::ptr::null_mut();
    v_res_24_ = l_Std_TreeSet_iter(v_00_u03b1_21_, v_cmp_22_, v_m_23_);
    lean_dec(v_m_23_);
    lean_dec_ref(v_cmp_22_);
    return v_res_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Iterator(builtin);
}
