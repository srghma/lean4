// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Vector
// Imports: Init.Data.Vector.Basic Std.Data.Iterators.Producers.Monadic.Array
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Std::Data::Iterators::Producers::Monadic::Array::{
    initialize_Std_Data_Iterators_Producers_Monadic_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Vector_iterFromIdxM___redArg(
    mut v_xs_34_: *mut LeanObject,
    mut v_pos_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_36_, 0, v_xs_34_);
    lean_ctor_set(v___x_36_, 1, v_pos_35_);
    return v___x_36_;
}
pub unsafe fn l_Vector_iterFromIdxM(
    mut v_00_u03b1_37_: *mut LeanObject,
    mut v_n_38_: *mut LeanObject,
    mut v_xs_39_: *mut LeanObject,
    mut v_m_40_: *mut LeanObject,
    mut v_pos_41_: *mut LeanObject,
    mut v_inst_42_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    v___x_43_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_43_, 0, v_xs_39_);
    lean_ctor_set(v___x_43_, 1, v_pos_41_);
    return v___x_43_;
}
pub unsafe fn l_Vector_iterFromIdxM___boxed(
    mut v_00_u03b1_44_: *mut LeanObject,
    mut v_n_45_: *mut LeanObject,
    mut v_xs_46_: *mut LeanObject,
    mut v_m_47_: *mut LeanObject,
    mut v_pos_48_: *mut LeanObject,
    mut v_inst_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Vector_iterFromIdxM(
        v_00_u03b1_44_,
        v_n_45_,
        v_xs_46_,
        v_m_47_,
        v_pos_48_,
        v_inst_49_,
    );
    lean_dec(v_inst_49_);
    lean_dec(v_n_45_);
    return v_res_50_;
}
pub unsafe fn l_Vector_iterM___redArg(mut v_xs_51_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    v___x_52_ = lean_unsigned_to_nat(0);
    v___x_53_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_53_, 0, v_xs_51_);
    lean_ctor_set(v___x_53_, 1, v___x_52_);
    return v___x_53_;
}
pub unsafe fn l_Vector_iterM(
    mut v_00_u03b1_54_: *mut LeanObject,
    mut v_n_55_: *mut LeanObject,
    mut v_xs_56_: *mut LeanObject,
    mut v_m_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    v___x_59_ = lean_unsigned_to_nat(0);
    v___x_60_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_60_, 0, v_xs_56_);
    lean_ctor_set(v___x_60_, 1, v___x_59_);
    return v___x_60_;
}
pub unsafe fn l_Vector_iterM___boxed(
    mut v_00_u03b1_61_: *mut LeanObject,
    mut v_n_62_: *mut LeanObject,
    mut v_xs_63_: *mut LeanObject,
    mut v_m_64_: *mut LeanObject,
    mut v_inst_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Vector_iterM(v_00_u03b1_61_, v_n_62_, v_xs_63_, v_m_64_, v_inst_65_);
    lean_dec(v_inst_65_);
    lean_dec(v_n_62_);
    return v_res_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Monadic_Vector(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Monadic_Vector(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
}
