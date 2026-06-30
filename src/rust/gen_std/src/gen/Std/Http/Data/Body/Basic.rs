// Lean compiler output
// Module: Std.Http.Data.Body.Basic
// Imports: Std.Async Std.Async.ContextAsync Std.Http.Data.Chunk Std.Http.Data.Headers Std.Http.Data.Body.Length
use crate::ffi::{lean_string_from_utf8_unchecked, lean_string_validate_utf8};
use crate::r#gen::Init::Data::String::Defs::l_String_toUTF8___boxed;
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Std::Async::ContextAsync::{
    initialize_Std_Async_ContextAsync, runtime_initialize_Std_Async_ContextAsync,
};
use crate::r#gen::Std::Async::{initialize_Std_Async, runtime_initialize_Std_Async};
use crate::r#gen::Std::Http::Data::Body::Length::{
    initialize_Std_Http_Data_Body_Length, runtime_initialize_Std_Http_Data_Body_Length,
};
use crate::r#gen::Std::Http::Data::Chunk::{
    initialize_Std_Http_Data_Chunk, runtime_initialize_Std_Http_Data_Chunk,
};
use crate::r#gen::Std::Http::Data::Headers::{
    initialize_Std_Http_Data_Headers, runtime_initialize_Std_Http_Data_Headers,
};
pub static l_Std_Http_Body_instToByteArrayByteArray___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_instToByteArrayByteArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instToByteArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instToByteArrayByteArray: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instToByteArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instToByteArrayString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_toUTF8___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instToByteArrayString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instToByteArrayString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instToByteArrayString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instToByteArrayString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instFromByteArrayByteArray___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instFromByteArrayByteArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instFromByteArrayByteArray: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 101, 110, 99, 111, 100, 105,
        110, 103, 0,
    ],
};
static mut l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFromByteArrayString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instFromByteArrayString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instFromByteArrayString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instFromByteArrayString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFromByteArrayString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Body_instFromByteArrayByteArray___lam__0(
    mut v_a_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_24_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_24_, 0, v_a_23_);
    return v___x_24_;
}
pub unsafe fn l_Std_Http_Body_instFromByteArrayString___lam__0(
    mut v_bs_30_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_31_: u8 = 0;
    v___x_31_ = lean_string_validate_utf8(v_bs_30_);
    if v___x_31_ == 0 {
        let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_bs_30_);
        v___x_32_ = l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1;
        return v___x_32_;
    } else {
        let mut v___x_33_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_34_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_33_ = lean_string_from_utf8_unchecked(v_bs_30_);
        v___x_34_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_34_, 0, v___x_33_);
        return v___x_34_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Async(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_ContextAsync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Chunk(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Headers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Basic(
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
pub unsafe fn initialize_Std_Http_Data_Body_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Async(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_ContextAsync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Chunk(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Headers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Body_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Basic(builtin);
}