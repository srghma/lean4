// Lean compiler output
// Module: Init.Data.List.FinRange
// Imports: Init.Data.List.OfFn Init.Data.List.Control Init.Data.List.OfFn Init.Data.List.Monadic
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::List::OfFn::{
    initialize_Init_Data_List_OfFn, l_List_ofFn___redArg, runtime_initialize_Init_Data_List_OfFn,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok,
};
pub static l_List_finRange___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_finRange___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_finRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_finRange___closed__0_value) as *mut LeanObject;
pub unsafe fn l_List_finRange___lam__0(mut v_i_8_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_i_8_);
    return v_i_8_;
}
pub unsafe fn l_List_finRange___lam__0___boxed(mut v_i_9_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_10_: *mut LeanObject = core::ptr::null_mut();
    v_res_10_ = l_List_finRange___lam__0(v_i_9_);
    lean_dec(v_i_9_);
    return v_res_10_;
}
pub unsafe fn l_List_finRange(mut v_n_12_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_13_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_14_: *mut LeanObject = core::ptr::null_mut();
    v___f_13_ = l_List_finRange___closed__0;
    v___x_14_ = l_List_ofFn___redArg(v_n_12_, v___f_13_);
    return v___x_14_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_FinRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_FinRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_FinRange(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_FinRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_FinRange(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_FinRange(builtin);
}
