// Lean compiler output
// Module: Init.Data.Cast
// Imports: Init.Coe
use crate::r#gen::Init::Coe::{initialize_Init_Coe, runtime_initialize_Init_Coe};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_instNatCastNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instNatCastNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instNatCastNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instNatCastNat___closed__0_value) as *mut LeanObject;
pub static mut l_instNatCastNat: *mut LeanObject =
    core::ptr::addr_of!(l_instNatCastNat___closed__0_value) as *mut LeanObject;
pub unsafe fn l_instNatCastNat___lam__0(mut v_n_23_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_n_23_);
    return v_n_23_;
}
pub unsafe fn l_instNatCastNat___lam__0___boxed(mut v_n_24_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_25_: *mut LeanObject = core::ptr::null_mut();
    v_res_25_ = l_instNatCastNat___lam__0(v_n_24_);
    lean_dec(v_n_24_);
    return v_res_25_;
}
pub unsafe fn l_Nat_cast___redArg(
    mut v_inst_28_: *mut LeanObject,
    mut v_a_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_30_: *mut LeanObject = core::ptr::null_mut();
    v___x_30_ = lean_apply_1(v_inst_28_, v_a_29_);
    return v___x_30_;
}
pub unsafe fn l_Nat_cast(
    mut v_R_31_: *mut LeanObject,
    mut v_inst_32_: *mut LeanObject,
    mut v_a_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    v___x_34_ = lean_apply_1(v_inst_32_, v_a_33_);
    return v___x_34_;
}
pub unsafe fn l_instCoeTailNatOfNatCast___redArg(
    mut v_inst_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_36_ = lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_36_, 0, lean_box(0));
    lean_closure_set(v___x_36_, 1, v_inst_35_);
    return v___x_36_;
}
pub unsafe fn l_instCoeTailNatOfNatCast(
    mut v_R_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_39_ = lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_39_, 0, lean_box(0));
    lean_closure_set(v___x_39_, 1, v_inst_38_);
    return v___x_39_;
}
pub unsafe fn l_instCoeHTCTNatOfNatCast___redArg(
    mut v_inst_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    v___x_41_ = lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_41_, 0, lean_box(0));
    lean_closure_set(v___x_41_, 1, v_inst_40_);
    return v___x_41_;
}
pub unsafe fn l_instCoeHTCTNatOfNatCast(
    mut v_R_42_: *mut LeanObject,
    mut v_inst_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v___x_44_ = lean_alloc_closure(l_Nat_cast as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_44_, 0, lean_box(0));
    lean_closure_set(v___x_44_, 1, v_inst_43_);
    return v___x_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Cast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Cast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Cast(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Cast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Cast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Cast(builtin);
}
