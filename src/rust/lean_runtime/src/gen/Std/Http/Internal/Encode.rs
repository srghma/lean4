// Lean compiler output
// Module: Std.Http.Internal.Encode
// Imports: Std.Http.Internal.ChunkedBuffer Std.Http.Data.Version
use crate::r#gen::Std::Http::Data::Version::{
    initialize_Std_Http_Data_Version, runtime_initialize_Std_Http_Data_Version,
};
use crate::r#gen::Std::Http::Internal::ChunkedBuffer::{
    initialize_Std_Http_Internal_ChunkedBuffer, runtime_initialize_Std_Http_Internal_ChunkedBuffer,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_to_utf8;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_byte_array_size, lean_nat_add};
pub static l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 49, 46, 48, 0],
};
static mut l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 49, 46, 49, 0],
};
static mut l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 50, 46, 48, 0],
};
static mut l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 84, 84, 80, 47, 51, 46, 48, 0],
};
static mut l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instEncodeV11Version___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instEncodeV11Version___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_instEncodeV11Version: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instEncodeV11Version___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Internal_instEncodeV11Version___lam__0(
    mut v_buffer_36_: *mut crate::leanh::LeanObject,
    mut v___y_37_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_44_: u8 = 0;
    let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_52_: u8 = 0;
    let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v___y_37_ {
                0 => {
                    v___x_53_ = l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0;
                    v___y_39_ = v___x_53_;
                    state = 1;
                    continue;
                }
                1 => {
                    v___x_54_ = l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1;
                    v___y_39_ = v___x_54_;
                    state = 1;
                    continue;
                }
                2 => {
                    v___x_55_ = l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2;
                    v___y_39_ = v___x_55_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___x_56_ = l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3;
                    v___y_39_ = v___x_56_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v_data_40_ = crate::leanh::lean_ctor_get(v_buffer_36_, 0);
                v_size_41_ = crate::leanh::lean_ctor_get(v_buffer_36_, 1);
                v_isSharedCheck_52_ = (!crate::leanh::lean_is_exclusive(v_buffer_36_)) as u8;
                if v_isSharedCheck_52_ == 0 {
                    v___x_43_ = v_buffer_36_;
                    v_isShared_44_ = v_isSharedCheck_52_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_41_);
                    crate::leanh::lean_inc(v_data_40_);
                    crate::leanh::lean_dec(v_buffer_36_);
                    v___x_43_ = crate::leanh::lean_box(0);
                    v_isShared_44_ = v_isSharedCheck_52_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_45_ = lean_string_to_utf8(v___y_39_);
                crate::leanh::lean_inc_ref(v___x_45_);
                v___x_46_ = lean_array_push(v_data_40_, v___x_45_);
                v___x_47_ = lean_byte_array_size(v___x_45_);
                crate::leanh::lean_dec_ref(v___x_45_);
                v___x_48_ = lean_nat_add(v_size_41_, v___x_47_);
                crate::leanh::lean_dec(v_size_41_);
                if v_isShared_44_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_43_, 1, v___x_48_);
                    crate::leanh::lean_ctor_set(v___x_43_, 0, v___x_46_);
                    v___x_50_ = v___x_43_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_51_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_46_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_51_, 1, v___x_48_);
                    v___x_50_ = v_reuseFailAlloc_51_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_50_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(
    mut v_buffer_57_: *mut crate::leanh::LeanObject,
    mut v___y_58_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_52__boxed_59_: u8 = 0;
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_52__boxed_59_ = (crate::leanh::lean_unbox(v___y_58_) as u8);
    v_res_60_ =
        l_Std_Http_Internal_instEncodeV11Version___lam__0(v_buffer_57_, v___y_52__boxed_59_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_Encode(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_Encode(
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
pub unsafe fn initialize_Std_Http_Internal_Encode(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_Encode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_Encode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_Encode(builtin);
}
