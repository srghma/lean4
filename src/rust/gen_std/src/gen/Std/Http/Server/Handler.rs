// Lean compiler output
// Module: Std.Http.Server.Handler
// Imports: Std.Async Std.Http.Data Std.Async.ContextAsync
use crate::r#gen::Std::Async::ContextAsync::{
    initialize_Std_Async_ContextAsync, runtime_initialize_Std_Async_ContextAsync,
};
use crate::r#gen::Std::Async::{initialize_Std_Async, runtime_initialize_Std_Async};
use crate::r#gen::Std::Http::Data::Body::Any::l_Std_Http_Body_instAny;
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
pub static l_Std_Http_Server_instHandlerStatelessHandler___closed__0_value:
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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value:
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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value:
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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Server_instHandlerStatelessHandler: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_Handler_ofFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_Handler_ofFn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_Handler_ofFn___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_Handler_ofFn___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__0(
    mut v_self_94_: *mut leanh::LeanObject,
    mut v_request_95_: *mut leanh::LeanObject,
    mut v___y_96_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_onRequest_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_onRequest_98_ = leanh::lean_ctor_get(v_self_94_, 0);
    leanh::lean_inc_ref(v_onRequest_98_);
    leanh::lean_dec_ref(v_self_94_);
    leanh::lean_inc_ref(v___y_96_);
    v___x_99_ = leanh::lean_apply_3(
        v_onRequest_98_,
        v_request_95_,
        v___y_96_,
        leanh::lean_box(0),
    );
    return v___x_99_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed(
    mut v_self_100_: *mut leanh::LeanObject,
    mut v_request_101_: *mut leanh::LeanObject,
    mut v___y_102_: *mut leanh::LeanObject,
    mut v___y_103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_104_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__0(
        v_self_100_,
        v_request_101_,
        v___y_102_,
    );
    leanh::lean_dec_ref(v___y_102_);
    return v_res_104_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__1(
    mut v_self_105_: *mut leanh::LeanObject,
    mut v_error_106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_onFailure_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_onFailure_108_ = leanh::lean_ctor_get(v_self_105_, 1);
    leanh::lean_inc_ref(v_onFailure_108_);
    leanh::lean_dec_ref(v_self_105_);
    v___x_109_ =
        leanh::lean_apply_2(v_onFailure_108_, v_error_106_, leanh::lean_box(0));
    return v___x_109_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed(
    mut v_self_110_: *mut leanh::LeanObject,
    mut v_error_111_: *mut leanh::LeanObject,
    mut v___y_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_113_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__1(v_self_110_, v_error_111_);
    return v_res_113_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__2(
    mut v_self_114_: *mut leanh::LeanObject,
    mut v_request_115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_onContinue_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_onContinue_117_ = leanh::lean_ctor_get(v_self_114_, 2);
    leanh::lean_inc_ref(v_onContinue_117_);
    leanh::lean_dec_ref(v_self_114_);
    v___x_118_ =
        leanh::lean_apply_2(v_onContinue_117_, v_request_115_, leanh::lean_box(0));
    return v___x_118_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed(
    mut v_self_119_: *mut leanh::LeanObject,
    mut v_request_120_: *mut leanh::LeanObject,
    mut v___y_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ =
        l_Std_Http_Server_instHandlerStatelessHandler___lam__2(v_self_119_, v_request_120_);
    return v_res_122_;
}
pub unsafe fn _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3()
-> *mut leanh::LeanObject {
    let mut v___f_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_126_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__2;
    v___f_127_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__1;
    v___f_128_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__0;
    v___x_129_ = l_Std_Http_Body_instAny;
    v___x_130_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_130_, 0, v___x_129_);
    leanh::lean_ctor_set(v___x_130_, 1, v___f_128_);
    leanh::lean_ctor_set(v___x_130_, 2, v___f_127_);
    leanh::lean_ctor_set(v___x_130_, 3, v___f_126_);
    return v___x_130_;
}
pub unsafe fn _init_l_Std_Http_Server_instHandlerStatelessHandler() -> *mut leanh::LeanObject
{
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_131_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Server_instHandlerStatelessHandler___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once),
        _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3,
    );
    return v___x_131_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__0(
    mut v_x_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = l_Std_Http_Server_Handler_ofFn___lam__0___closed__1;
    return v___x_138_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__0___boxed(
    mut v_x_139_: *mut leanh::LeanObject,
    mut v___y_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Std_Http_Server_Handler_ofFn___lam__0(v_x_139_);
    leanh::lean_dec(v_x_139_);
    return v_res_141_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__1(
    mut v_x_147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Std_Http_Server_Handler_ofFn___lam__1___closed__1;
    return v___x_149_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__1___boxed(
    mut v_x_150_: *mut leanh::LeanObject,
    mut v___y_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Std_Http_Server_Handler_ofFn___lam__1(v_x_150_);
    leanh::lean_dec_ref(v_x_150_);
    return v_res_152_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn(
    mut v_f_155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_156_ = l_Std_Http_Server_Handler_ofFn___closed__0;
    v___f_157_ = l_Std_Http_Server_Handler_ofFn___closed__1;
    v___x_158_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_158_, 0, v_f_155_);
    leanh::lean_ctor_set(v___x_158_, 1, v___f_156_);
    leanh::lean_ctor_set(v___x_158_, 2, v___f_157_);
    return v___x_158_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFns(
    mut v_onRequest_159_: *mut leanh::LeanObject,
    mut v_onFailure_160_: *mut leanh::LeanObject,
    mut v_onContinue_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_162_, 0, v_onRequest_159_);
    leanh::lean_ctor_set(v___x_162_, 1, v_onFailure_160_);
    leanh::lean_ctor_set(v___x_162_, 2, v_onContinue_161_);
    return v___x_162_;
}
pub unsafe fn l_Std_Http_Server_Handler_withFailure(
    mut v_handler_163_: *mut leanh::LeanObject,
    mut v_onFailure_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_onRequest_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onContinue_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_169_: u8 = 0;
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_173_: u8 = 0;
    let mut v_unused_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_onRequest_165_ = leanh::lean_ctor_get(v_handler_163_, 0);
                v_onContinue_166_ = leanh::lean_ctor_get(v_handler_163_, 2);
                v_isSharedCheck_173_ = (!leanh::lean_is_exclusive(v_handler_163_)) as u8;
                if v_isSharedCheck_173_ == 0 {
                    v_unused_174_ = leanh::lean_ctor_get(v_handler_163_, 1);
                    leanh::lean_dec(v_unused_174_);
                    v___x_168_ = v_handler_163_;
                    v_isShared_169_ = v_isSharedCheck_173_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_onContinue_166_);
                    leanh::lean_inc(v_onRequest_165_);
                    leanh::lean_dec(v_handler_163_);
                    v___x_168_ = leanh::lean_box(0);
                    v_isShared_169_ = v_isSharedCheck_173_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_169_ == 0 {
                    leanh::lean_ctor_set(v___x_168_, 1, v_onFailure_164_);
                    v___x_171_ = v___x_168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_172_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_172_, 0, v_onRequest_165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_172_, 1, v_onFailure_164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_172_, 2, v_onContinue_166_);
                    v___x_171_ = v_reuseFailAlloc_172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_Handler_withContinue(
    mut v_handler_175_: *mut leanh::LeanObject,
    mut v_onContinue_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_onRequest_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onFailure_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_181_: u8 = 0;
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_185_: u8 = 0;
    let mut v_unused_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_onRequest_177_ = leanh::lean_ctor_get(v_handler_175_, 0);
                v_onFailure_178_ = leanh::lean_ctor_get(v_handler_175_, 1);
                v_isSharedCheck_185_ = (!leanh::lean_is_exclusive(v_handler_175_)) as u8;
                if v_isSharedCheck_185_ == 0 {
                    v_unused_186_ = leanh::lean_ctor_get(v_handler_175_, 2);
                    leanh::lean_dec(v_unused_186_);
                    v___x_180_ = v_handler_175_;
                    v_isShared_181_ = v_isSharedCheck_185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_onFailure_178_);
                    leanh::lean_inc(v_onRequest_177_);
                    leanh::lean_dec(v_handler_175_);
                    v___x_180_ = leanh::lean_box(0);
                    v_isShared_181_ = v_isSharedCheck_185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_181_ == 0 {
                    leanh::lean_ctor_set(v___x_180_, 2, v_onContinue_176_);
                    v___x_183_ = v___x_180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_184_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_184_, 0, v_onRequest_177_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_184_, 1, v_onFailure_178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_184_, 2, v_onContinue_176_);
                    v___x_183_ = v_reuseFailAlloc_184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_183_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Server_Handler(
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
    res = runtime_initialize_Std_Http_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_ContextAsync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Http_Server_instHandlerStatelessHandler =
        _init_l_Std_Http_Server_instHandlerStatelessHandler();
    leanh::lean_mark_persistent(l_Std_Http_Server_instHandlerStatelessHandler);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server_Handler(
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
pub unsafe fn initialize_Std_Http_Server_Handler(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Std_Http_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_ContextAsync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Handler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server_Handler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Server_Handler(builtin);
}