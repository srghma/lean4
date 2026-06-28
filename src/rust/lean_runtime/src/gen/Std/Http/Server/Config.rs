// Lean compiler output
// Module: Std.Http.Server.Config
// Imports: Std.Time Std.Http.Protocol.H1
use crate::r#gen::Std::Http::Protocol::H1::{
    initialize_Std_Http_Protocol_H1, runtime_initialize_Std_Http_Protocol_H1,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec_ref, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Http_Config_toH1Config(mut v_config_24_: *mut LeanObject) -> *mut LeanObject {
    let mut v_maxRequests_25_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeaders_26_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderBytes_27_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enableKeepAlive_28_: u8 = 0;
    let mut v_serverName_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxUriLength_30_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxStartLineLength_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderNameLength_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderValueLength_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxSpaceSequence_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxLeadingEmptyLines_35_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtNameLength_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtValueLength_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxChunkLineLength_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxChunkSize_39_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxBodySize_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxReasonPhraseLength_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxTrailerHeaders_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtensions_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
    v_maxRequests_25_ = lean_ctor_get(v_config_24_, 1);
    v_maxHeaders_26_ = lean_ctor_get(v_config_24_, 2);
    v_maxHeaderBytes_27_ = lean_ctor_get(v_config_24_, 3);
    v_enableKeepAlive_28_ = lean_ctor_get_uint8(
        v_config_24_,
        (core::mem::size_of::<*mut LeanObject>() * 24) as u32,
    );
    v_serverName_29_ = lean_ctor_get(v_config_24_, 9);
    v_maxUriLength_30_ = lean_ctor_get(v_config_24_, 10);
    v_maxStartLineLength_31_ = lean_ctor_get(v_config_24_, 11);
    v_maxHeaderNameLength_32_ = lean_ctor_get(v_config_24_, 12);
    v_maxHeaderValueLength_33_ = lean_ctor_get(v_config_24_, 13);
    v_maxSpaceSequence_34_ = lean_ctor_get(v_config_24_, 14);
    v_maxLeadingEmptyLines_35_ = lean_ctor_get(v_config_24_, 15);
    v_maxChunkExtNameLength_36_ = lean_ctor_get(v_config_24_, 16);
    v_maxChunkExtValueLength_37_ = lean_ctor_get(v_config_24_, 17);
    v_maxChunkLineLength_38_ = lean_ctor_get(v_config_24_, 18);
    v_maxChunkSize_39_ = lean_ctor_get(v_config_24_, 19);
    v_maxBodySize_40_ = lean_ctor_get(v_config_24_, 20);
    v_maxReasonPhraseLength_41_ = lean_ctor_get(v_config_24_, 21);
    v_maxTrailerHeaders_42_ = lean_ctor_get(v_config_24_, 22);
    v_maxChunkExtensions_43_ = lean_ctor_get(v_config_24_, 23);
    lean_inc(v_maxTrailerHeaders_42_);
    lean_inc(v_maxReasonPhraseLength_41_);
    lean_inc(v_maxBodySize_40_);
    lean_inc(v_maxChunkSize_39_);
    lean_inc(v_maxChunkLineLength_38_);
    lean_inc(v_maxChunkExtValueLength_37_);
    lean_inc(v_maxChunkExtNameLength_36_);
    lean_inc(v_maxChunkExtensions_43_);
    lean_inc(v_maxLeadingEmptyLines_35_);
    lean_inc(v_maxSpaceSequence_34_);
    lean_inc(v_maxHeaderValueLength_33_);
    lean_inc(v_maxHeaderNameLength_32_);
    lean_inc(v_maxStartLineLength_31_);
    lean_inc(v_maxUriLength_30_);
    lean_inc(v_serverName_29_);
    lean_inc(v_maxHeaderBytes_27_);
    lean_inc(v_maxHeaders_26_);
    lean_inc(v_maxRequests_25_);
    v___x_44_ = lean_alloc_ctor(0, 18, (1) as u32);
    lean_ctor_set(v___x_44_, 0, v_maxRequests_25_);
    lean_ctor_set(v___x_44_, 1, v_maxHeaders_26_);
    lean_ctor_set(v___x_44_, 2, v_maxHeaderBytes_27_);
    lean_ctor_set(v___x_44_, 3, v_serverName_29_);
    lean_ctor_set(v___x_44_, 4, v_maxUriLength_30_);
    lean_ctor_set(v___x_44_, 5, v_maxStartLineLength_31_);
    lean_ctor_set(v___x_44_, 6, v_maxHeaderNameLength_32_);
    lean_ctor_set(v___x_44_, 7, v_maxHeaderValueLength_33_);
    lean_ctor_set(v___x_44_, 8, v_maxSpaceSequence_34_);
    lean_ctor_set(v___x_44_, 9, v_maxLeadingEmptyLines_35_);
    lean_ctor_set(v___x_44_, 10, v_maxChunkExtensions_43_);
    lean_ctor_set(v___x_44_, 11, v_maxChunkExtNameLength_36_);
    lean_ctor_set(v___x_44_, 12, v_maxChunkExtValueLength_37_);
    lean_ctor_set(v___x_44_, 13, v_maxChunkLineLength_38_);
    lean_ctor_set(v___x_44_, 14, v_maxChunkSize_39_);
    lean_ctor_set(v___x_44_, 15, v_maxBodySize_40_);
    lean_ctor_set(v___x_44_, 16, v_maxReasonPhraseLength_41_);
    lean_ctor_set(v___x_44_, 17, v_maxTrailerHeaders_42_);
    lean_ctor_set_uint8(
        v___x_44_,
        (core::mem::size_of::<*mut LeanObject>() * 18) as u32,
        v_enableKeepAlive_28_,
    );
    return v___x_44_;
}
pub unsafe fn l_Std_Http_Config_toH1Config___boxed(
    mut v_config_45_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_46_: *mut LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_Http_Config_toH1Config(v_config_45_);
    lean_dec_ref(v_config_45_);
    return v_res_46_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Server_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Server_Config(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Server_Config(builtin);
}
