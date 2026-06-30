// Lean compiler output
// Module: Init.Data.Vector.Stream
// Imports: Init.Data.Stream Init.Data.Vector.Basic Init.Data.Slice.Array.Basic
use crate::ffi::lean_array_get_size;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Basic::{
    initialize_Init_Data_Slice_Array_Basic, runtime_initialize_Init_Data_Slice_Array_Basic,
};
use crate::r#gen::Init::Data::Stream::{
    initialize_Init_Data_Stream, runtime_initialize_Init_Data_Stream,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
pub static l_Vector_instToStreamSubarray___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Vector_instToStreamSubarray___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_instToStreamSubarray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_instToStreamSubarray___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Vector_instToStreamSubarray___lam__0(
    mut v_xs_12_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_15_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13_ = leanh::lean_unsigned_to_nat(0);
    v___x_14_ = lean_array_get_size(v_xs_12_);
    v___x_15_ = l_Array_toSubarray___redArg(v_xs_12_, v___x_13_, v___x_14_);
    return v___x_15_;
}
pub unsafe fn l_Vector_instToStreamSubarray(
    mut v_00_u03b1_17_: *mut leanh::LeanObject,
    mut v_n_18_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_19_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_19_ = l_Vector_instToStreamSubarray___closed__0;
    return v___f_19_;
}
pub unsafe fn l_Vector_instToStreamSubarray___boxed(
    mut v_00_u03b1_20_: *mut leanh::LeanObject,
    mut v_n_21_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_22_ = l_Vector_instToStreamSubarray(v_00_u03b1_20_, v_n_21_);
    leanh::lean_dec(v_n_21_);
    return v_res_22_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Stream(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Stream(
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
pub unsafe fn initialize_Init_Data_Vector_Stream(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Stream(builtin);
}