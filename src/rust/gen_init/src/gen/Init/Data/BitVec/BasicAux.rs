// Lean compiler output
// Module: Init.Data.BitVec.BasicAux
// Imports: Init.Grind.Tactics
use crate::ffi::{lean_nat_add, lean_nat_pow, lean_nat_sub};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
pub unsafe fn l_BitVec_instOfNat(
    mut v_n_32_: *mut crate::leanh::LeanObject,
    mut v_i_33_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34_ = l_BitVec_ofNat(v_n_32_, v_i_33_);
    return v___x_34_;
}
pub unsafe fn l_BitVec_instOfNat___boxed(
    mut v_n_35_: *mut crate::leanh::LeanObject,
    mut v_i_36_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_37_ = l_BitVec_instOfNat(v_n_35_, v_i_36_);
    crate::leanh::lean_dec(v_i_36_);
    crate::leanh::lean_dec(v_n_35_);
    return v_res_37_;
}
pub unsafe fn l_BitVec_add(
    mut v_n_38_: *mut crate::leanh::LeanObject,
    mut v_x_39_: *mut crate::leanh::LeanObject,
    mut v_y_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = lean_nat_add(v_x_39_, v_y_40_);
    v___x_42_ = l_BitVec_ofNat(v_n_38_, v___x_41_);
    crate::leanh::lean_dec(v___x_41_);
    return v___x_42_;
}
pub unsafe fn l_BitVec_add___boxed(
    mut v_n_43_: *mut crate::leanh::LeanObject,
    mut v_x_44_: *mut crate::leanh::LeanObject,
    mut v_y_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_BitVec_add(v_n_43_, v_x_44_, v_y_45_);
    crate::leanh::lean_dec(v_y_45_);
    crate::leanh::lean_dec(v_x_44_);
    crate::leanh::lean_dec(v_n_43_);
    return v_res_46_;
}
pub unsafe fn l_BitVec_instAdd(
    mut v_n_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_48_ =
        crate::leanh::lean_alloc_closure(l_BitVec_add___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_48_, 0, v_n_47_);
    return v___x_48_;
}
pub unsafe fn l_BitVec_sub(
    mut v_n_49_: *mut crate::leanh::LeanObject,
    mut v_x_50_: *mut crate::leanh::LeanObject,
    mut v_y_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_52_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_53_ = lean_nat_pow(v___x_52_, v_n_49_);
    v___x_54_ = lean_nat_sub(v___x_53_, v_y_51_);
    crate::leanh::lean_dec(v___x_53_);
    v___x_55_ = lean_nat_add(v___x_54_, v_x_50_);
    crate::leanh::lean_dec(v___x_54_);
    v___x_56_ = l_BitVec_ofNat(v_n_49_, v___x_55_);
    crate::leanh::lean_dec(v___x_55_);
    return v___x_56_;
}
pub unsafe fn l_BitVec_sub___boxed(
    mut v_n_57_: *mut crate::leanh::LeanObject,
    mut v_x_58_: *mut crate::leanh::LeanObject,
    mut v_y_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_BitVec_sub(v_n_57_, v_x_58_, v_y_59_);
    crate::leanh::lean_dec(v_y_59_);
    crate::leanh::lean_dec(v_x_58_);
    crate::leanh::lean_dec(v_n_57_);
    return v_res_60_;
}
pub unsafe fn l_BitVec_instSub(
    mut v_n_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ =
        crate::leanh::lean_alloc_closure(l_BitVec_sub___boxed as *mut core::ffi::c_void, 3, 1);
    crate::leanh::lean_closure_set(v___x_62_, 0, v_n_61_);
    return v___x_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_BasicAux(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_BasicAux(
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
pub unsafe fn initialize_Init_Data_BitVec_BasicAux(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_BasicAux(builtin);
}
