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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_BundledIterM_ofIterM___redArg(
    mut v_inst_36_: *mut LeanObject,
    mut v_it_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    v___x_38_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_38_, 0, v_inst_36_);
    lean_ctor_set(v___x_38_, 1, v_it_37_);
    return v___x_38_;
}
pub unsafe fn l_Std_BundledIterM_ofIterM(
    mut v_m_39_: *mut LeanObject,
    mut v_00_u03b2_40_: *mut LeanObject,
    mut v_00_u03b1_41_: *mut LeanObject,
    mut v_inst_42_: *mut LeanObject,
    mut v_it_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_44_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_44_, 0, v_inst_42_);
    lean_ctor_set(v___x_44_, 1, v_it_43_);
    return v___x_44_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg(mut v_bit_45_: *mut LeanObject) -> *mut LeanObject {
    let mut v_inst_46_: *mut LeanObject = core::ptr::null_mut();
    v_inst_46_ = lean_ctor_get(v_bit_45_, 0);
    lean_inc(v_inst_46_);
    return v_inst_46_;
}
pub unsafe fn l_Std_instIterator_u03b1___redArg___boxed(
    mut v_bit_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_48_: *mut LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_instIterator_u03b1___redArg(v_bit_47_);
    lean_dec_ref(v_bit_47_);
    return v_res_48_;
}
pub unsafe fn l_Std_instIterator_u03b1(
    mut v_m_49_: *mut LeanObject,
    mut v_00_u03b2_50_: *mut LeanObject,
    mut v_bit_51_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_52_: *mut LeanObject = core::ptr::null_mut();
    v_inst_52_ = lean_ctor_get(v_bit_51_, 0);
    lean_inc(v_inst_52_);
    return v_inst_52_;
}
pub unsafe fn l_Std_instIterator_u03b1___boxed(
    mut v_m_53_: *mut LeanObject,
    mut v_00_u03b2_54_: *mut LeanObject,
    mut v_bit_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_instIterator_u03b1(v_m_53_, v_00_u03b2_54_, v_bit_55_);
    lean_dec_ref(v_bit_55_);
    return v_res_56_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(
    mut v_a_57_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_57_);
    return v_a_57_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg___boxed(
    mut v_a_58_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_59_: *mut LeanObject = core::ptr::null_mut();
    v_res_59_ =
        l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___redArg(v_a_58_);
    lean_dec(v_a_58_);
    return v_res_59_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
    mut v_00_u03b1_60_: *mut LeanObject,
    mut v_R_61_: *mut LeanObject,
    mut v_S_62_: *mut LeanObject,
    mut v_h_63_: *mut LeanObject,
    mut v_a_64_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_64_);
    return v_a_64_;
}
pub unsafe fn l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot___boxed(
    mut v_00_u03b1_65_: *mut LeanObject,
    mut v_R_66_: *mut LeanObject,
    mut v_S_67_: *mut LeanObject,
    mut v_h_68_: *mut LeanObject,
    mut v_a_69_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_70_: *mut LeanObject = core::ptr::null_mut();
    v_res_70_ = l___private_Std_Data_Iterators_Lemmas_Equivalence_Basic_0__Std_quotOfQuot(
        v_00_u03b1_65_,
        v_R_66_,
        v_S_67_,
        v_h_68_,
        v_a_69_,
    );
    lean_dec(v_a_69_);
    return v_res_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
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
pub unsafe fn initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Internal_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Lemmas_Equivalence_HetT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Lemmas_Equivalence_Basic(builtin);
}
