// Lean compiler output
// Module: Std.Http.Server.Config
// Imports: Std.Time Std.Http.Protocol.H1
use crate::r#gen::Std::Http::Protocol::H1::{
    initialize_Std_Http_Protocol_H1, runtime_initialize_Std_Http_Protocol_H1,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub unsafe fn l_Std_Http_Config_toH1Config(
    mut v_config_24_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_maxRequests_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeaders_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderBytes_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enableKeepAlive_28_: u8 = 0;
    let mut v_serverName_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUriLength_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxStartLineLength_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderNameLength_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeaderValueLength_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSpaceSequence_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxLeadingEmptyLines_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtNameLength_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtValueLength_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxChunkLineLength_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxChunkSize_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxBodySize_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxReasonPhraseLength_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxTrailerHeaders_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxChunkExtensions_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_maxRequests_25_ = crate::leanh::lean_ctor_get(v_config_24_, 1);
    v_maxHeaders_26_ = crate::leanh::lean_ctor_get(v_config_24_, 2);
    v_maxHeaderBytes_27_ = crate::leanh::lean_ctor_get(v_config_24_, 3);
    v_enableKeepAlive_28_ = crate::leanh::lean_ctor_get_uint8(
        v_config_24_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 24) as u32,
    );
    v_serverName_29_ = crate::leanh::lean_ctor_get(v_config_24_, 9);
    v_maxUriLength_30_ = crate::leanh::lean_ctor_get(v_config_24_, 10);
    v_maxStartLineLength_31_ = crate::leanh::lean_ctor_get(v_config_24_, 11);
    v_maxHeaderNameLength_32_ = crate::leanh::lean_ctor_get(v_config_24_, 12);
    v_maxHeaderValueLength_33_ = crate::leanh::lean_ctor_get(v_config_24_, 13);
    v_maxSpaceSequence_34_ = crate::leanh::lean_ctor_get(v_config_24_, 14);
    v_maxLeadingEmptyLines_35_ = crate::leanh::lean_ctor_get(v_config_24_, 15);
    v_maxChunkExtNameLength_36_ = crate::leanh::lean_ctor_get(v_config_24_, 16);
    v_maxChunkExtValueLength_37_ = crate::leanh::lean_ctor_get(v_config_24_, 17);
    v_maxChunkLineLength_38_ = crate::leanh::lean_ctor_get(v_config_24_, 18);
    v_maxChunkSize_39_ = crate::leanh::lean_ctor_get(v_config_24_, 19);
    v_maxBodySize_40_ = crate::leanh::lean_ctor_get(v_config_24_, 20);
    v_maxReasonPhraseLength_41_ = crate::leanh::lean_ctor_get(v_config_24_, 21);
    v_maxTrailerHeaders_42_ = crate::leanh::lean_ctor_get(v_config_24_, 22);
    v_maxChunkExtensions_43_ = crate::leanh::lean_ctor_get(v_config_24_, 23);
    crate::leanh::lean_inc(v_maxTrailerHeaders_42_);
    crate::leanh::lean_inc(v_maxReasonPhraseLength_41_);
    crate::leanh::lean_inc(v_maxBodySize_40_);
    crate::leanh::lean_inc(v_maxChunkSize_39_);
    crate::leanh::lean_inc(v_maxChunkLineLength_38_);
    crate::leanh::lean_inc(v_maxChunkExtValueLength_37_);
    crate::leanh::lean_inc(v_maxChunkExtNameLength_36_);
    crate::leanh::lean_inc(v_maxChunkExtensions_43_);
    crate::leanh::lean_inc(v_maxLeadingEmptyLines_35_);
    crate::leanh::lean_inc(v_maxSpaceSequence_34_);
    crate::leanh::lean_inc(v_maxHeaderValueLength_33_);
    crate::leanh::lean_inc(v_maxHeaderNameLength_32_);
    crate::leanh::lean_inc(v_maxStartLineLength_31_);
    crate::leanh::lean_inc(v_maxUriLength_30_);
    crate::leanh::lean_inc(v_serverName_29_);
    crate::leanh::lean_inc(v_maxHeaderBytes_27_);
    crate::leanh::lean_inc(v_maxHeaders_26_);
    crate::leanh::lean_inc(v_maxRequests_25_);
    v___x_44_ = crate::leanh::lean_alloc_ctor(0, 18, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_44_, 0, v_maxRequests_25_);
    crate::leanh::lean_ctor_set(v___x_44_, 1, v_maxHeaders_26_);
    crate::leanh::lean_ctor_set(v___x_44_, 2, v_maxHeaderBytes_27_);
    crate::leanh::lean_ctor_set(v___x_44_, 3, v_serverName_29_);
    crate::leanh::lean_ctor_set(v___x_44_, 4, v_maxUriLength_30_);
    crate::leanh::lean_ctor_set(v___x_44_, 5, v_maxStartLineLength_31_);
    crate::leanh::lean_ctor_set(v___x_44_, 6, v_maxHeaderNameLength_32_);
    crate::leanh::lean_ctor_set(v___x_44_, 7, v_maxHeaderValueLength_33_);
    crate::leanh::lean_ctor_set(v___x_44_, 8, v_maxSpaceSequence_34_);
    crate::leanh::lean_ctor_set(v___x_44_, 9, v_maxLeadingEmptyLines_35_);
    crate::leanh::lean_ctor_set(v___x_44_, 10, v_maxChunkExtensions_43_);
    crate::leanh::lean_ctor_set(v___x_44_, 11, v_maxChunkExtNameLength_36_);
    crate::leanh::lean_ctor_set(v___x_44_, 12, v_maxChunkExtValueLength_37_);
    crate::leanh::lean_ctor_set(v___x_44_, 13, v_maxChunkLineLength_38_);
    crate::leanh::lean_ctor_set(v___x_44_, 14, v_maxChunkSize_39_);
    crate::leanh::lean_ctor_set(v___x_44_, 15, v_maxBodySize_40_);
    crate::leanh::lean_ctor_set(v___x_44_, 16, v_maxReasonPhraseLength_41_);
    crate::leanh::lean_ctor_set(v___x_44_, 17, v_maxTrailerHeaders_42_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_44_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 18) as u32,
        v_enableKeepAlive_28_,
    );
    return v___x_44_;
}
pub unsafe fn l_Std_Http_Config_toH1Config___boxed(
    mut v_config_45_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_46_ = l_Std_Http_Config_toH1Config(v_config_45_);
    crate::leanh::lean_dec_ref(v_config_45_);
    return v_res_46_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Server_Config(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Server_Config(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Server_Config(builtin);
}
