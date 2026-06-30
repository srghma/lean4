// Lean compiler output
// Module: Std.Data.TreeMap.Iterator
// Imports: Std.Data.TreeMap.Basic Std.Data.DTreeMap.Iterator Init.Data.Iterators.Lemmas.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Zipper::l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg;
use crate::r#gen::Std::Data::DTreeMap::Iterator::{
    initialize_Std_Data_DTreeMap_Iterator, runtime_initialize_Std_Data_DTreeMap_Iterator,
};
use crate::r#gen::Std::Data::TreeMap::Basic::{
    initialize_Std_Data_TreeMap_Basic, runtime_initialize_Std_Data_TreeMap_Basic,
};
pub unsafe fn l_Std_TreeMap_iter___redArg(
    mut v_m_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_44_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_TreeMap_iter___redArg___boxed(
    mut v_m_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_TreeMap_iter___redArg(v_m_45_);
    leanh::lean_dec(v_m_45_);
    return v_res_46_;
}
pub unsafe fn l_Std_TreeMap_iter(
    mut v_00_u03b1_47_: *mut leanh::LeanObject,
    mut v_00_u03b2_48_: *mut leanh::LeanObject,
    mut v_cmp_49_: *mut leanh::LeanObject,
    mut v_m_50_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_50_);
    return v___x_51_;
}
pub unsafe fn l_Std_TreeMap_iter___boxed(
    mut v_00_u03b1_52_: *mut leanh::LeanObject,
    mut v_00_u03b2_53_: *mut leanh::LeanObject,
    mut v_cmp_54_: *mut leanh::LeanObject,
    mut v_m_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_TreeMap_iter(v_00_u03b1_52_, v_00_u03b2_53_, v_cmp_54_, v_m_55_);
    leanh::lean_dec(v_m_55_);
    leanh::lean_dec_ref(v_cmp_54_);
    return v_res_56_;
}
pub unsafe fn l_Std_TreeMap_keysIter___redArg(
    mut v_m_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_58_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_57_);
    return v___x_58_;
}
pub unsafe fn l_Std_TreeMap_keysIter___redArg___boxed(
    mut v_m_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_TreeMap_keysIter___redArg(v_m_59_);
    leanh::lean_dec(v_m_59_);
    return v_res_60_;
}
pub unsafe fn l_Std_TreeMap_keysIter(
    mut v_00_u03b1_61_: *mut leanh::LeanObject,
    mut v_00_u03b2_62_: *mut leanh::LeanObject,
    mut v_cmp_63_: *mut leanh::LeanObject,
    mut v_m_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_65_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_64_);
    return v___x_65_;
}
pub unsafe fn l_Std_TreeMap_keysIter___boxed(
    mut v_00_u03b1_66_: *mut leanh::LeanObject,
    mut v_00_u03b2_67_: *mut leanh::LeanObject,
    mut v_cmp_68_: *mut leanh::LeanObject,
    mut v_m_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l_Std_TreeMap_keysIter(v_00_u03b1_66_, v_00_u03b2_67_, v_cmp_68_, v_m_69_);
    leanh::lean_dec(v_m_69_);
    leanh::lean_dec_ref(v_cmp_68_);
    return v_res_70_;
}
pub unsafe fn l_Std_TreeMap_valuesIter___redArg(
    mut v_m_71_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_72_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_71_);
    return v___x_72_;
}
pub unsafe fn l_Std_TreeMap_valuesIter___redArg___boxed(
    mut v_m_73_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_74_ = l_Std_TreeMap_valuesIter___redArg(v_m_73_);
    leanh::lean_dec(v_m_73_);
    return v_res_74_;
}
pub unsafe fn l_Std_TreeMap_valuesIter(
    mut v_00_u03b1_75_: *mut leanh::LeanObject,
    mut v_00_u03b2_76_: *mut leanh::LeanObject,
    mut v_cmp_77_: *mut leanh::LeanObject,
    mut v_m_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = l_Std_DTreeMap_Internal_Zipper_iterOfTree___redArg(v_m_78_);
    return v___x_79_;
}
pub unsafe fn l_Std_TreeMap_valuesIter___boxed(
    mut v_00_u03b1_80_: *mut leanh::LeanObject,
    mut v_00_u03b2_81_: *mut leanh::LeanObject,
    mut v_cmp_82_: *mut leanh::LeanObject,
    mut v_m_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_84_ = l_Std_TreeMap_valuesIter(v_00_u03b1_80_, v_00_u03b2_81_, v_cmp_82_, v_m_83_);
    leanh::lean_dec(v_m_83_);
    leanh::lean_dec_ref(v_cmp_82_);
    return v_res_84_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeMap_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeMap_Iterator(
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
pub unsafe fn initialize_Std_Data_TreeMap_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_TreeMap_Iterator(builtin);
}