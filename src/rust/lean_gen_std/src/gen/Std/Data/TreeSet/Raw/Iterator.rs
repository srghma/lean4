// Lean compiler output
// Module: Std.Data.TreeSet.Raw.Iterator
// Imports: Std.Data.TreeSet.Raw.Basic Std.Data.TreeMap.Raw.Iterator Std.Data.DTreeMap.Raw.Lemmas Init.Data.Iterators.Lemmas.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Zipper::l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg;
use crate::r#gen::Std::Data::DTreeMap::Raw::Lemmas::{
    initialize_Std_Data_DTreeMap_Raw_Lemmas, runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Iterator::{
    initialize_Std_Data_TreeMap_Raw_Iterator, runtime_initialize_Std_Data_TreeMap_Raw_Iterator,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Basic::{
    initialize_Std_Data_TreeSet_Raw_Basic, runtime_initialize_Std_Data_TreeSet_Raw_Basic,
};
pub unsafe fn l_Std_TreeSet_Raw_iter___redArg(
    mut v_m_13_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_13_);
    return v___x_14_;
}
pub unsafe fn l_Std_TreeSet_Raw_iter___redArg___boxed(
    mut v_m_15_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_16_ = l_Std_TreeSet_Raw_iter___redArg(v_m_15_);
    crate::leanh::lean_dec(v_m_15_);
    return v_res_16_;
}
pub unsafe fn l_Std_TreeSet_Raw_iter(
    mut v_00_u03b1_17_: *mut crate::leanh::LeanObject,
    mut v_cmp_18_: *mut crate::leanh::LeanObject,
    mut v_m_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_20_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_19_);
    return v___x_20_;
}
pub unsafe fn l_Std_TreeSet_Raw_iter___boxed(
    mut v_00_u03b1_21_: *mut crate::leanh::LeanObject,
    mut v_cmp_22_: *mut crate::leanh::LeanObject,
    mut v_m_23_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_24_ = l_Std_TreeSet_Raw_iter(v_00_u03b1_21_, v_cmp_22_, v_m_23_);
    crate::leanh::lean_dec(v_m_23_);
    crate::leanh::lean_dec_ref(v_cmp_22_);
    return v_res_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Raw_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Raw_Iterator(
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
pub unsafe fn initialize_Std_Data_TreeSet_Raw_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Raw_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Raw_Iterator(builtin);
}
