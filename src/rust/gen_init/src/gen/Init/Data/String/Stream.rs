// Lean compiler output
// Module: Init.Data.String.Stream
// Imports: Init.Data.String.Basic Init.Data.Stream
use crate::ffi::{lean_nat_dec_lt, lean_string_utf8_get, lean_string_utf8_next};
use crate::r#gen::Init::Data::Stream::{
    initialize_Init_Data_Stream, runtime_initialize_Init_Data_Stream,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
pub static l_instStreamRawChar___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instStreamRawChar___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instStreamRawChar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instStreamRawChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instStreamRawChar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instStreamRawChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_instStreamRawChar___lam__0(
    mut v_s_21_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_27_: u8 = 0;
    let mut v___x_28_: u8 = 0;
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: u32 = 0;
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_38_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_22_ = crate::leanh::lean_ctor_get(v_s_21_, 0);
                v_startPos_23_ = crate::leanh::lean_ctor_get(v_s_21_, 1);
                v_stopPos_24_ = crate::leanh::lean_ctor_get(v_s_21_, 2);
                v_isSharedCheck_38_ = (!crate::leanh::lean_is_exclusive(v_s_21_)) as u8;
                if v_isSharedCheck_38_ == 0 {
                    v___x_26_ = v_s_21_;
                    v_isShared_27_ = v_isSharedCheck_38_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stopPos_24_);
                    crate::leanh::lean_inc(v_startPos_23_);
                    crate::leanh::lean_inc(v_str_22_);
                    crate::leanh::lean_dec(v_s_21_);
                    v___x_26_ = crate::leanh::lean_box(0);
                    v_isShared_27_ = v_isSharedCheck_38_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_28_ = lean_nat_dec_lt(v_startPos_23_, v_stopPos_24_);
                if v___x_28_ == 0 {
                    crate::leanh::lean_del_object(v___x_26_);
                    crate::leanh::lean_dec(v_stopPos_24_);
                    crate::leanh::lean_dec(v_startPos_23_);
                    crate::leanh::lean_dec_ref(v_str_22_);
                    v___x_29_ = crate::leanh::lean_box(0);
                    return v___x_29_;
                } else {
                    v___x_30_ = lean_string_utf8_get(v_str_22_, v_startPos_23_);
                    v___x_31_ = lean_string_utf8_next(v_str_22_, v_startPos_23_);
                    crate::leanh::lean_dec(v_startPos_23_);
                    if v_isShared_27_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_26_, 1, v___x_31_);
                        v___x_33_ = v___x_26_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_37_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_37_, 0, v_str_22_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_31_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_37_, 2, v_stopPos_24_);
                        v___x_33_ = v_reuseFailAlloc_37_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_34_ = crate::leanh::lean_box_uint32(v___x_30_);
                v___x_35_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_35_, 0, v___x_34_);
                crate::leanh::lean_ctor_set(v___x_35_, 1, v___x_33_);
                v___x_36_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_36_, 0, v___x_35_);
                return v___x_36_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Stream(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Stream(
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
pub unsafe fn initialize_Init_Data_String_Stream(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Stream(builtin);
}
