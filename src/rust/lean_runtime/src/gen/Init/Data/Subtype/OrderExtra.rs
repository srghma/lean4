// Lean compiler output
// Module: Init.Data.Subtype.OrderExtra
// Imports: Init.Data.Ord.Basic
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_2, lean_box, lean_closure_set,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub unsafe fn l_instOrdSubtype___redArg___lam__0(
    mut v_inst_17_: *mut LeanObject,
    mut v_a_18_: *mut LeanObject,
    mut v_b_19_: *mut LeanObject,
) -> u8 {
    let mut v___x_20_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_21_: u8 = 0;
    v___x_20_ = lean_apply_2(v_inst_17_, v_a_18_, v_b_19_);
    v___x_21_ = (lean_unbox(v___x_20_) as u8);
    return v___x_21_;
}
pub unsafe fn l_instOrdSubtype___redArg___lam__0___boxed(
    mut v_inst_22_: *mut LeanObject,
    mut v_a_23_: *mut LeanObject,
    mut v_b_24_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_25_: u8 = 0;
    let mut v_r_26_: *mut LeanObject = core::ptr::null_mut();
    v_res_25_ = l_instOrdSubtype___redArg___lam__0(v_inst_22_, v_a_23_, v_b_24_);
    v_r_26_ = lean_box((v_res_25_) as usize);
    return v_r_26_;
}
pub unsafe fn l_instOrdSubtype___redArg(mut v_inst_27_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_28_: *mut LeanObject = core::ptr::null_mut();
    v___f_28_ = lean_alloc_closure(
        l_instOrdSubtype___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_28_, 0, v_inst_27_);
    return v___f_28_;
}
pub unsafe fn l_instOrdSubtype(
    mut v_00_u03b1_29_: *mut LeanObject,
    mut v_inst_30_: *mut LeanObject,
    mut v_P_31_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_32_: *mut LeanObject = core::ptr::null_mut();
    v___f_32_ = lean_alloc_closure(
        l_instOrdSubtype___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_32_, 0, v_inst_30_);
    return v___f_32_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Subtype_OrderExtra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Subtype_OrderExtra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Subtype_OrderExtra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_OrderExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Subtype_OrderExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Subtype_OrderExtra(builtin);
}
