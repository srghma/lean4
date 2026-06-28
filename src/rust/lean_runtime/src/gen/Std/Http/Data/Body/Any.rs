// Lean compiler output
// Module: Std.Http.Data.Body.Any
// Imports: Std.Http.Data.Body.Basic
use crate::r#gen::Std::Http::Data::Body::Basic::{
    initialize_Std_Http_Data_Body_Basic, runtime_initialize_Std_Http_Data_Body_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
};
pub static l_Std_Http_Body_instAny___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__5_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instAny___lam__6___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instAny___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__6_value) as *mut LeanObject;
pub static l_Std_Http_Body_instAny___closed__7_value: LeanCtorObject<7> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_instAny___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__7_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instAny___closed__7_value) as *mut LeanObject;
pub unsafe fn l_Std_Http_Body_Any_ofBody___redArg(
    mut v_inst_92_: *mut LeanObject,
    mut v_body_93_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recv_94_: *mut LeanObject = core::ptr::null_mut();
    let mut v_close_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isClosed_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvSelector_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryRecv_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getKnownSize_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_setKnownSize_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_103_: u8 = 0;
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_recv_94_ = lean_ctor_get(v_inst_92_, 0);
                v_close_95_ = lean_ctor_get(v_inst_92_, 1);
                v_isClosed_96_ = lean_ctor_get(v_inst_92_, 2);
                v_recvSelector_97_ = lean_ctor_get(v_inst_92_, 3);
                v_tryRecv_98_ = lean_ctor_get(v_inst_92_, 4);
                v_getKnownSize_99_ = lean_ctor_get(v_inst_92_, 5);
                v_setKnownSize_100_ = lean_ctor_get(v_inst_92_, 6);
                v_isSharedCheck_114_ = (!lean_is_exclusive(v_inst_92_)) as u8;
                if v_isSharedCheck_114_ == 0 {
                    v___x_102_ = v_inst_92_;
                    v_isShared_103_ = v_isSharedCheck_114_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_setKnownSize_100_);
                    lean_inc(v_getKnownSize_99_);
                    lean_inc(v_tryRecv_98_);
                    lean_inc(v_recvSelector_97_);
                    lean_inc(v_isClosed_96_);
                    lean_inc(v_close_95_);
                    lean_inc(v_recv_94_);
                    lean_dec(v_inst_92_);
                    v___x_102_ = lean_box(0);
                    v_isShared_103_ = v_isSharedCheck_114_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_body_93_, 6);
                v___x_104_ = lean_apply_1(v_recv_94_, v_body_93_);
                v___x_105_ = lean_apply_1(v_close_95_, v_body_93_);
                v___x_106_ = lean_apply_1(v_isClosed_96_, v_body_93_);
                v___x_107_ = lean_apply_1(v_recvSelector_97_, v_body_93_);
                v___x_108_ = lean_apply_1(v_tryRecv_98_, v_body_93_);
                v___x_109_ = lean_apply_1(v_getKnownSize_99_, v_body_93_);
                v___x_110_ = lean_apply_1(v_setKnownSize_100_, v_body_93_);
                if v_isShared_103_ == 0 {
                    lean_ctor_set(v___x_102_, 6, v___x_110_);
                    lean_ctor_set(v___x_102_, 5, v___x_109_);
                    lean_ctor_set(v___x_102_, 4, v___x_108_);
                    lean_ctor_set(v___x_102_, 3, v___x_107_);
                    lean_ctor_set(v___x_102_, 2, v___x_106_);
                    lean_ctor_set(v___x_102_, 1, v___x_105_);
                    lean_ctor_set(v___x_102_, 0, v___x_104_);
                    v___x_112_ = v___x_102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_104_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_105_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 2, v___x_106_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 3, v___x_107_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 4, v___x_108_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 5, v___x_109_);
                    lean_ctor_set(v_reuseFailAlloc_113_, 6, v___x_110_);
                    v___x_112_ = v_reuseFailAlloc_113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Any_ofBody(
    mut v_00_u03b1_115_: *mut LeanObject,
    mut v_inst_116_: *mut LeanObject,
    mut v_body_117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
    v___x_118_ = l_Std_Http_Body_Any_ofBody___redArg(v_inst_116_, v_body_117_);
    return v___x_118_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__0(
    mut v_self_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recv_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    v_recv_121_ = lean_ctor_get(v_self_119_, 0);
    lean_inc_ref(v_recv_121_);
    lean_dec_ref(v_self_119_);
    v___x_122_ = lean_apply_1(v_recv_121_, lean_box(0));
    return v___x_122_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__0___boxed(
    mut v_self_123_: *mut LeanObject,
    mut v___y_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_125_: *mut LeanObject = core::ptr::null_mut();
    v_res_125_ = l_Std_Http_Body_instAny___lam__0(v_self_123_);
    return v_res_125_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__1(
    mut v_self_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_close_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    v_close_128_ = lean_ctor_get(v_self_126_, 1);
    lean_inc_ref(v_close_128_);
    lean_dec_ref(v_self_126_);
    v___x_129_ = lean_apply_1(v_close_128_, lean_box(0));
    return v___x_129_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__1___boxed(
    mut v_self_130_: *mut LeanObject,
    mut v___y_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_132_: *mut LeanObject = core::ptr::null_mut();
    v_res_132_ = l_Std_Http_Body_instAny___lam__1(v_self_130_);
    return v_res_132_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__2(
    mut v_self_133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isClosed_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    v_isClosed_135_ = lean_ctor_get(v_self_133_, 2);
    lean_inc_ref(v_isClosed_135_);
    lean_dec_ref(v_self_133_);
    v___x_136_ = lean_apply_1(v_isClosed_135_, lean_box(0));
    return v___x_136_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__2___boxed(
    mut v_self_137_: *mut LeanObject,
    mut v___y_138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_139_: *mut LeanObject = core::ptr::null_mut();
    v_res_139_ = l_Std_Http_Body_instAny___lam__2(v_self_137_);
    return v_res_139_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__3(
    mut v_self_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recvSelector_141_: *mut LeanObject = core::ptr::null_mut();
    v_recvSelector_141_ = lean_ctor_get(v_self_140_, 3);
    lean_inc_ref(v_recvSelector_141_);
    return v_recvSelector_141_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__3___boxed(
    mut v_self_142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_143_: *mut LeanObject = core::ptr::null_mut();
    v_res_143_ = l_Std_Http_Body_instAny___lam__3(v_self_142_);
    lean_dec_ref(v_self_142_);
    return v_res_143_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__4(
    mut v_self_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryRecv_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    v_tryRecv_146_ = lean_ctor_get(v_self_144_, 4);
    lean_inc_ref(v_tryRecv_146_);
    lean_dec_ref(v_self_144_);
    v___x_147_ = lean_apply_1(v_tryRecv_146_, lean_box(0));
    return v___x_147_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__4___boxed(
    mut v_self_148_: *mut LeanObject,
    mut v___y_149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_150_: *mut LeanObject = core::ptr::null_mut();
    v_res_150_ = l_Std_Http_Body_instAny___lam__4(v_self_148_);
    return v_res_150_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__5(
    mut v_self_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getKnownSize_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    v_getKnownSize_153_ = lean_ctor_get(v_self_151_, 5);
    lean_inc_ref(v_getKnownSize_153_);
    lean_dec_ref(v_self_151_);
    v___x_154_ = lean_apply_1(v_getKnownSize_153_, lean_box(0));
    return v___x_154_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__5___boxed(
    mut v_self_155_: *mut LeanObject,
    mut v___y_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_157_: *mut LeanObject = core::ptr::null_mut();
    v_res_157_ = l_Std_Http_Body_instAny___lam__5(v_self_155_);
    return v_res_157_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__6(
    mut v_self_158_: *mut LeanObject,
    mut v___y_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_setKnownSize_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    v_setKnownSize_161_ = lean_ctor_get(v_self_158_, 6);
    lean_inc_ref(v_setKnownSize_161_);
    lean_dec_ref(v_self_158_);
    v___x_162_ = lean_apply_2(v_setKnownSize_161_, v___y_159_, lean_box(0));
    return v___x_162_;
}
pub unsafe fn l_Std_Http_Body_instAny___lam__6___boxed(
    mut v_self_163_: *mut LeanObject,
    mut v___y_164_: *mut LeanObject,
    mut v___y_165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_166_: *mut LeanObject = core::ptr::null_mut();
    v_res_166_ = l_Std_Http_Body_instAny___lam__6(v_self_163_, v___y_164_);
    return v_res_166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Any(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_Body_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Any(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Body_Any(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_Body_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Any(builtin);
}
