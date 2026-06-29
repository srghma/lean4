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
    mut v_inst_36_: *mut crate::leanh::LeanObject,
    mut v_it_37_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_38_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_38_, 0, v_inst_36_);
    crate::leanh::lean_ctor_set(v___x_38_, 1, v_it_37_);
    return v___x_38_;
}
pub unsafe fn l_Std_BundledIterM_ofIterM(
    mut v_m_39_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_40_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_41_: *mut crate::leanh::LeanObject,
    mut v_inst_42_: *mut crate::leanh::LeanObject,
    mut v_it_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_44_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_44_, 0, v_inst_42_);
    crate::leanh::lean_ctor_set(v___x_44_, 1, v_it_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg(
    mut v_bit_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_46_ = crate::leanh::lean_ctor_get(v_bit_45_, 0);
    crate::leanh::lean_inc(v_inst_46_);
    return v_inst_46_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg___boxed(
    mut v_bit_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_instIterator_u03b1___redArg(v_bit_47_);
    crate::leanh::lean_dec_ref(v_bit_47_);
    return v_res_48_;
}
pub unsafe fn l_Std_instIterator_u03b1(
    mut v_m_49_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_50_: *mut crate::leanh::LeanObject,
    mut v_bit_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inst_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inst_52_ = crate::leanh::lean_ctor_get(v_bit_51_, 0);
    crate::leanh::lean_inc(v_inst_52_);
    return v_inst_52_;
}
pub unsafe fn l_Std_instIterator_u03b1___boxed(
    mut v_m_53_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_54_: *mut crate::leanh::LeanObject,
    mut v_bit_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_instIterator_u03b1(v_m_53_, v_00_u03b2_54_, v_bit_55_);
    crate::leanh::lean_dec_ref(v_bit_55_);
    return v_res_56_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(
    mut v_a_57_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_57_);
    return v_a_57_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg___boxed(
    mut v_a_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_59_ =
        l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(v_a_58_);
    crate::leanh::lean_dec(v_a_58_);
    return v_res_59_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
    mut v_00_u03b1_60_: *mut crate::leanh::LeanObject,
    mut v_R_61_: *mut crate::leanh::LeanObject,
    mut v_S_62_: *mut crate::leanh::LeanObject,
    mut v_h_63_: *mut crate::leanh::LeanObject,
    mut v_a_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_a_64_);
    return v_a_64_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___boxed(
    mut v_00_u03b1_65_: *mut crate::leanh::LeanObject,
    mut v_R_66_: *mut crate::leanh::LeanObject,
    mut v_S_67_: *mut crate::leanh::LeanObject,
    mut v_h_68_: *mut crate::leanh::LeanObject,
    mut v_a_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_70_ = l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
        v_00_u03b1_65_,
        v_R_66_,
        v_S_67_,
        v_h_68_,
        v_a_69_,
    );
    crate::leanh::lean_dec(v_a_69_);
    return v_res_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
}
