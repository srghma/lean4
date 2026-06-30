// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Equivalence.Basic
// Imports: Init.Internal.Order Init.Data.Iterators.Basic Std.Data.Iterators.Lemmas.Equivalence.HetT
use crate::r#gen::Init::Data::Iterators::Basic::{
    initialize_Init_Data_Iterators_Basic, runtime_initialize_Init_Data_Iterators_Basic,
};
use crate::r#gen::Init::Internal::Order::{
    initialize_Init_Internal_Order, runtime_initialize_Init_Internal_Order,
};
use crate::r#gen::Std::Data::Iterators::Lemmas::Equivalence::HetT::{
    initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT,
    runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT,
};
pub unsafe fn l_Std_BundledIterM_ofIterM___redArg(
    mut v_inst_36_: *mut leanh::LeanObject,
    mut v_it_37_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_38_, 0, v_inst_36_);
    leanh::lean_ctor_set(v___x_38_, 1, v_it_37_);
    return v___x_38_;
}
pub unsafe fn l_Std_BundledIterM_ofIterM(
    mut v_m_39_: *mut leanh::LeanObject,
    mut v_00_u03b2_40_: *mut leanh::LeanObject,
    mut v_00_u03b1_41_: *mut leanh::LeanObject,
    mut v_inst_42_: *mut leanh::LeanObject,
    mut v_it_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_44_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_44_, 0, v_inst_42_);
    leanh::lean_ctor_set(v___x_44_, 1, v_it_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg(
    mut v_bit_45_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_46_ = leanh::lean_ctor_get(v_bit_45_, 0);
    leanh::lean_inc(v_inst_46_);
    return v_inst_46_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg___boxed(
    mut v_bit_47_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_48_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_instIterator_u03b1___redArg(v_bit_47_);
    leanh::lean_dec_ref(v_bit_47_);
    return v_res_48_;
}
pub unsafe fn l_Std_instIterator_u03b1(
    mut v_m_49_: *mut leanh::LeanObject,
    mut v_00_u03b2_50_: *mut leanh::LeanObject,
    mut v_bit_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inst_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inst_52_ = leanh::lean_ctor_get(v_bit_51_, 0);
    leanh::lean_inc(v_inst_52_);
    return v_inst_52_;
}
pub unsafe fn l_Std_instIterator_u03b1___boxed(
    mut v_m_53_: *mut leanh::LeanObject,
    mut v_00_u03b2_54_: *mut leanh::LeanObject,
    mut v_bit_55_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_instIterator_u03b1(v_m_53_, v_00_u03b2_54_, v_bit_55_);
    leanh::lean_dec_ref(v_bit_55_);
    return v_res_56_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(
    mut v_a_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_57_);
    return v_a_57_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg___boxed(
    mut v_a_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_59_ =
        l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(v_a_58_);
    leanh::lean_dec(v_a_58_);
    return v_res_59_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
    mut v_00_u03b1_60_: *mut leanh::LeanObject,
    mut v_R_61_: *mut leanh::LeanObject,
    mut v_S_62_: *mut leanh::LeanObject,
    mut v_h_63_: *mut leanh::LeanObject,
    mut v_a_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_64_);
    return v_a_64_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___boxed(
    mut v_00_u03b1_65_: *mut leanh::LeanObject,
    mut v_R_66_: *mut leanh::LeanObject,
    mut v_S_67_: *mut leanh::LeanObject,
    mut v_h_68_: *mut leanh::LeanObject,
    mut v_a_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
        v_00_u03b1_65_,
        v_R_66_,
        v_S_67_,
        v_h_68_,
        v_a_69_,
    );
    leanh::lean_dec(v_a_69_);
    return v_res_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
}