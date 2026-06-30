// Lean compiler output
// Module: Init.GrindInstances.Ring.BitVec
// Imports: Init.GrindInstances.ToInt Init.Data.BitVec.Basic Init.Grind.ToInt Init.Data.BitVec.Lemmas Init.Grind.Ring.Basic Init.Data.BitVec.Bootstrap Init.Grind.Ring.ToInt
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, l_BitVec_instNatCast___lam__0___boxed,
    l_BitVec_instPowNat___lam__0___boxed, l_BitVec_mul, l_BitVec_mul___boxed, l_BitVec_neg___boxed,
    l_BitVec_ofInt, l_BitVec_ofInt___boxed, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::BasicAux::{
    l_BitVec_add___boxed, l_BitVec_instOfNat___boxed, l_BitVec_sub___boxed,
};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::Grind::Ring::ToInt::{
    initialize_Init_Grind_Ring_ToInt, runtime_initialize_Init_Grind_Ring_ToInt,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::r#gen::Init::GrindInstances::ToInt::{
    initialize_Init_GrindInstances_ToInt, runtime_initialize_Init_GrindInstances_ToInt,
};
use crate::r#gen::Init::Prelude::{l_BitVec_ofNat, l_instHAdd___redArg___lam__0};
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__0(
    mut v_w_33_: *mut leanh::LeanObject,
    mut v_x1_34_: *mut leanh::LeanObject,
    mut v_x2_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36_ = l_BitVec_ofNat(v_w_33_, v_x1_34_);
    v___x_37_ = l_BitVec_mul(v_w_33_, v___x_36_, v_x2_35_);
    leanh::lean_dec(v___x_36_);
    return v___x_37_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__0___boxed(
    mut v_w_38_: *mut leanh::LeanObject,
    mut v_x1_39_: *mut leanh::LeanObject,
    mut v_x2_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_41_ = l_Lean_Grind_instCommRingBitVec___lam__0(v_w_38_, v_x1_39_, v_x2_40_);
    leanh::lean_dec(v_x2_40_);
    leanh::lean_dec(v_x1_39_);
    leanh::lean_dec(v_w_38_);
    return v_res_41_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__1(
    mut v_w_42_: *mut leanh::LeanObject,
    mut v_x1_43_: *mut leanh::LeanObject,
    mut v_x2_44_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_45_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_45_ = l_BitVec_ofInt(v_w_42_, v_x1_43_);
    v___x_46_ = l_BitVec_mul(v_w_42_, v___x_45_, v_x2_44_);
    leanh::lean_dec(v___x_45_);
    return v___x_46_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__1___boxed(
    mut v_w_47_: *mut leanh::LeanObject,
    mut v_x1_48_: *mut leanh::LeanObject,
    mut v_x2_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Lean_Grind_instCommRingBitVec___lam__1(v_w_47_, v_x1_48_, v_x2_49_);
    leanh::lean_dec(v_x2_49_);
    leanh::lean_dec(v_x1_48_);
    leanh::lean_dec(v_w_47_);
    return v_res_50_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec(
    mut v_w_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_52_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_56_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_58_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_59_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_w_51_, 9);
    v___f_52_ = leanh::lean_alloc_closure(
        l_Lean_Grind_instCommRingBitVec___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_52_, 0, v_w_51_);
    v___f_53_ = leanh::lean_alloc_closure(
        l_Lean_Grind_instCommRingBitVec___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_53_, 0, v_w_51_);
    v___x_54_ =
        leanh::lean_alloc_closure(l_BitVec_add___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_54_, 0, v_w_51_);
    v___x_55_ =
        leanh::lean_alloc_closure(l_BitVec_mul___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_55_, 0, v_w_51_);
    v___f_56_ = leanh::lean_alloc_closure(
        l_BitVec_instNatCast___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_56_, 0, v_w_51_);
    v___x_57_ = leanh::lean_alloc_closure(
        l_BitVec_instOfNat___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_57_, 0, v_w_51_);
    v___f_58_ = leanh::lean_alloc_closure(
        l_BitVec_instPowNat___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_58_, 0, v_w_51_);
    v___f_59_ = leanh::lean_alloc_closure(
        l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_59_, 0, v___f_58_);
    v___x_60_ =
        leanh::lean_alloc_closure(l_BitVec_neg___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___x_60_, 0, v_w_51_);
    v___x_61_ =
        leanh::lean_alloc_closure(l_BitVec_sub___boxed as *mut core::ffi::c_void, 3, 1);
    leanh::lean_closure_set(v___x_61_, 0, v_w_51_);
    v___x_62_ =
        leanh::lean_alloc_closure(l_BitVec_ofInt___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___x_62_, 0, v_w_51_);
    v___x_63_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_63_, 0, v___x_54_);
    leanh::lean_ctor_set(v___x_63_, 1, v___x_55_);
    leanh::lean_ctor_set(v___x_63_, 2, v___f_56_);
    leanh::lean_ctor_set(v___x_63_, 3, v___x_57_);
    leanh::lean_ctor_set(v___x_63_, 4, v___f_52_);
    leanh::lean_ctor_set(v___x_63_, 5, v___f_59_);
    v___x_64_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_64_, 0, v___x_63_);
    leanh::lean_ctor_set(v___x_64_, 1, v___x_60_);
    leanh::lean_ctor_set(v___x_64_, 2, v___x_61_);
    leanh::lean_ctor_set(v___x_64_, 3, v___x_62_);
    leanh::lean_ctor_set(v___x_64_, 4, v___f_53_);
    return v___x_64_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_BitVec(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_BitVec(
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
pub unsafe fn initialize_Init_GrindInstances_Ring_BitVec(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_ToInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_BitVec(builtin);
}