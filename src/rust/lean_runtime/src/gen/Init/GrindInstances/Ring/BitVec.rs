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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__0(
    mut v_w_33_: *mut LeanObject,
    mut v_x1_34_: *mut LeanObject,
    mut v_x2_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = l_BitVec_ofNat(v_w_33_, v_x1_34_);
    v___x_37_ = l_BitVec_mul(v_w_33_, v___x_36_, v_x2_35_);
    lean_dec(v___x_36_);
    return v___x_37_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__0___boxed(
    mut v_w_38_: *mut LeanObject,
    mut v_x1_39_: *mut LeanObject,
    mut v_x2_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_41_: *mut LeanObject = core::ptr::null_mut();
    v_res_41_ = l_Lean_Grind_instCommRingBitVec___lam__0(v_w_38_, v_x1_39_, v_x2_40_);
    lean_dec(v_x2_40_);
    lean_dec(v_x1_39_);
    lean_dec(v_w_38_);
    return v_res_41_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__1(
    mut v_w_42_: *mut LeanObject,
    mut v_x1_43_: *mut LeanObject,
    mut v_x2_44_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
    v___x_45_ = l_BitVec_ofInt(v_w_42_, v_x1_43_);
    v___x_46_ = l_BitVec_mul(v_w_42_, v___x_45_, v_x2_44_);
    lean_dec(v___x_45_);
    return v___x_46_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec___lam__1___boxed(
    mut v_w_47_: *mut LeanObject,
    mut v_x1_48_: *mut LeanObject,
    mut v_x2_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Lean_Grind_instCommRingBitVec___lam__1(v_w_47_, v_x1_48_, v_x2_49_);
    lean_dec(v_x2_49_);
    lean_dec(v_x1_48_);
    lean_dec(v_w_47_);
    return v_res_50_;
}
pub unsafe fn l_Lean_Grind_instCommRingBitVec(mut v_w_51_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_56_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_58_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_w_51_, 9);
    v___f_52_ = lean_alloc_closure(
        l_Lean_Grind_instCommRingBitVec___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_52_, 0, v_w_51_);
    v___f_53_ = lean_alloc_closure(
        l_Lean_Grind_instCommRingBitVec___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_53_, 0, v_w_51_);
    v___x_54_ = lean_alloc_closure(l_BitVec_add___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___x_54_, 0, v_w_51_);
    v___x_55_ = lean_alloc_closure(l_BitVec_mul___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___x_55_, 0, v_w_51_);
    v___f_56_ = lean_alloc_closure(
        l_BitVec_instNatCast___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_56_, 0, v_w_51_);
    v___x_57_ = lean_alloc_closure(l_BitVec_instOfNat___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_57_, 0, v_w_51_);
    v___f_58_ = lean_alloc_closure(
        l_BitVec_instPowNat___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_58_, 0, v_w_51_);
    v___f_59_ = lean_alloc_closure(l_instHAdd___redArg___lam__0 as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_59_, 0, v___f_58_);
    v___x_60_ = lean_alloc_closure(l_BitVec_neg___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_60_, 0, v_w_51_);
    v___x_61_ = lean_alloc_closure(l_BitVec_sub___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___x_61_, 0, v_w_51_);
    v___x_62_ = lean_alloc_closure(l_BitVec_ofInt___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___x_62_, 0, v_w_51_);
    v___x_63_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_63_, 0, v___x_54_);
    lean_ctor_set(v___x_63_, 1, v___x_55_);
    lean_ctor_set(v___x_63_, 2, v___f_56_);
    lean_ctor_set(v___x_63_, 3, v___x_57_);
    lean_ctor_set(v___x_63_, 4, v___f_52_);
    lean_ctor_set(v___x_63_, 5, v___f_59_);
    v___x_64_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_64_, 0, v___x_63_);
    lean_ctor_set(v___x_64_, 1, v___x_60_);
    lean_ctor_set(v___x_64_, 2, v___x_61_);
    lean_ctor_set(v___x_64_, 3, v___x_62_);
    lean_ctor_set(v___x_64_, 4, v___f_53_);
    return v___x_64_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_BitVec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_BitVec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring_BitVec(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GrindInstances_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_BitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_BitVec(builtin);
}
