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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value:
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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value:
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
    m_fun: l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Server_instHandlerStatelessHandler___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Server_instHandlerStatelessHandler: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_Handler_ofFn___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_Handler_ofFn___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_Handler_ofFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_Handler_ofFn___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_Handler_ofFn___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_Handler_ofFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_Handler_ofFn___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__0(
    mut v_self_94_: *mut crate::leanh::LeanObject,
    mut v_request_95_: *mut crate::leanh::LeanObject,
    mut v___y_96_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onRequest_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_onRequest_98_ = crate::leanh::lean_ctor_get(v_self_94_, 0);
    crate::leanh::lean_inc_ref(v_onRequest_98_);
    crate::leanh::lean_dec_ref(v_self_94_);
    crate::leanh::lean_inc_ref(v___y_96_);
    v___x_99_ = crate::leanh::lean_apply_3(
        v_onRequest_98_,
        v_request_95_,
        v___y_96_,
        crate::leanh::lean_box(0),
    );
    return v___x_99_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed(
    mut v_self_100_: *mut crate::leanh::LeanObject,
    mut v_request_101_: *mut crate::leanh::LeanObject,
    mut v___y_102_: *mut crate::leanh::LeanObject,
    mut v___y_103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_104_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__0(
        v_self_100_,
        v_request_101_,
        v___y_102_,
    );
    crate::leanh::lean_dec_ref(v___y_102_);
    return v_res_104_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__1(
    mut v_self_105_: *mut crate::leanh::LeanObject,
    mut v_error_106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onFailure_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_onFailure_108_ = crate::leanh::lean_ctor_get(v_self_105_, 1);
    crate::leanh::lean_inc_ref(v_onFailure_108_);
    crate::leanh::lean_dec_ref(v_self_105_);
    v___x_109_ =
        crate::leanh::lean_apply_2(v_onFailure_108_, v_error_106_, crate::leanh::lean_box(0));
    return v___x_109_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed(
    mut v_self_110_: *mut crate::leanh::LeanObject,
    mut v_error_111_: *mut crate::leanh::LeanObject,
    mut v___y_112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_113_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__1(v_self_110_, v_error_111_);
    return v_res_113_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__2(
    mut v_self_114_: *mut crate::leanh::LeanObject,
    mut v_request_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onContinue_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_onContinue_117_ = crate::leanh::lean_ctor_get(v_self_114_, 2);
    crate::leanh::lean_inc_ref(v_onContinue_117_);
    crate::leanh::lean_dec_ref(v_self_114_);
    v___x_118_ =
        crate::leanh::lean_apply_2(v_onContinue_117_, v_request_115_, crate::leanh::lean_box(0));
    return v___x_118_;
}
pub unsafe fn l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed(
    mut v_self_119_: *mut crate::leanh::LeanObject,
    mut v_request_120_: *mut crate::leanh::LeanObject,
    mut v___y_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ =
        l_Std_Http_Server_instHandlerStatelessHandler___lam__2(v_self_119_, v_request_120_);
    return v_res_122_;
}
pub unsafe fn _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___f_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_126_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__2;
    v___f_127_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__1;
    v___f_128_ = l_Std_Http_Server_instHandlerStatelessHandler___closed__0;
    v___x_129_ = l_Std_Http_Body_instAny;
    v___x_130_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_130_, 0, v___x_129_);
    crate::leanh::lean_ctor_set(v___x_130_, 1, v___f_128_);
    crate::leanh::lean_ctor_set(v___x_130_, 2, v___f_127_);
    crate::leanh::lean_ctor_set(v___x_130_, 3, v___f_126_);
    return v___x_130_;
}
pub unsafe fn _init_l_Std_Http_Server_instHandlerStatelessHandler() -> *mut crate::leanh::LeanObject
{
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Server_instHandlerStatelessHandler___closed__3),
        core::ptr::addr_of_mut!(l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once),
        _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3,
    );
    return v___x_131_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__0(
    mut v_x_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = l_Std_Http_Server_Handler_ofFn___lam__0___closed__1;
    return v___x_138_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__0___boxed(
    mut v_x_139_: *mut crate::leanh::LeanObject,
    mut v___y_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_141_ = l_Std_Http_Server_Handler_ofFn___lam__0(v_x_139_);
    crate::leanh::lean_dec(v_x_139_);
    return v_res_141_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__1(
    mut v_x_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Std_Http_Server_Handler_ofFn___lam__1___closed__1;
    return v___x_149_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn___lam__1___boxed(
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v___y_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Std_Http_Server_Handler_ofFn___lam__1(v_x_150_);
    crate::leanh::lean_dec_ref(v_x_150_);
    return v_res_152_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFn(
    mut v_f_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_156_ = l_Std_Http_Server_Handler_ofFn___closed__0;
    v___f_157_ = l_Std_Http_Server_Handler_ofFn___closed__1;
    v___x_158_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_158_, 0, v_f_155_);
    crate::leanh::lean_ctor_set(v___x_158_, 1, v___f_156_);
    crate::leanh::lean_ctor_set(v___x_158_, 2, v___f_157_);
    return v___x_158_;
}
pub unsafe fn l_Std_Http_Server_Handler_ofFns(
    mut v_onRequest_159_: *mut crate::leanh::LeanObject,
    mut v_onFailure_160_: *mut crate::leanh::LeanObject,
    mut v_onContinue_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_162_, 0, v_onRequest_159_);
    crate::leanh::lean_ctor_set(v___x_162_, 1, v_onFailure_160_);
    crate::leanh::lean_ctor_set(v___x_162_, 2, v_onContinue_161_);
    return v___x_162_;
}
pub unsafe fn l_Std_Http_Server_Handler_withFailure(
    mut v_handler_163_: *mut crate::leanh::LeanObject,
    mut v_onFailure_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onRequest_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onContinue_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_169_: u8 = 0;
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_173_: u8 = 0;
    let mut v_unused_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_onRequest_165_ = crate::leanh::lean_ctor_get(v_handler_163_, 0);
                v_onContinue_166_ = crate::leanh::lean_ctor_get(v_handler_163_, 2);
                v_isSharedCheck_173_ = (!crate::leanh::lean_is_exclusive(v_handler_163_)) as u8;
                if v_isSharedCheck_173_ == 0 {
                    v_unused_174_ = crate::leanh::lean_ctor_get(v_handler_163_, 1);
                    crate::leanh::lean_dec(v_unused_174_);
                    v___x_168_ = v_handler_163_;
                    v_isShared_169_ = v_isSharedCheck_173_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_onContinue_166_);
                    crate::leanh::lean_inc(v_onRequest_165_);
                    crate::leanh::lean_dec(v_handler_163_);
                    v___x_168_ = crate::leanh::lean_box(0);
                    v_isShared_169_ = v_isSharedCheck_173_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_168_, 1, v_onFailure_164_);
                    v___x_171_ = v___x_168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_172_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_172_, 0, v_onRequest_165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_172_, 1, v_onFailure_164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_172_, 2, v_onContinue_166_);
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
    mut v_handler_175_: *mut crate::leanh::LeanObject,
    mut v_onContinue_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onRequest_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onFailure_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_181_: u8 = 0;
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_185_: u8 = 0;
    let mut v_unused_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_onRequest_177_ = crate::leanh::lean_ctor_get(v_handler_175_, 0);
                v_onFailure_178_ = crate::leanh::lean_ctor_get(v_handler_175_, 1);
                v_isSharedCheck_185_ = (!crate::leanh::lean_is_exclusive(v_handler_175_)) as u8;
                if v_isSharedCheck_185_ == 0 {
                    v_unused_186_ = crate::leanh::lean_ctor_get(v_handler_175_, 2);
                    crate::leanh::lean_dec(v_unused_186_);
                    v___x_180_ = v_handler_175_;
                    v_isShared_181_ = v_isSharedCheck_185_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_onFailure_178_);
                    crate::leanh::lean_inc(v_onRequest_177_);
                    crate::leanh::lean_dec(v_handler_175_);
                    v___x_180_ = crate::leanh::lean_box(0);
                    v_isShared_181_ = v_isSharedCheck_185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_181_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_180_, 2, v_onContinue_176_);
                    v___x_183_ = v___x_180_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_184_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_184_, 0, v_onRequest_177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_184_, 1, v_onFailure_178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_184_, 2, v_onContinue_176_);
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
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Async(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_ContextAsync(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Http_Server_instHandlerStatelessHandler =
        _init_l_Std_Http_Server_instHandlerStatelessHandler();
    crate::leanh::lean_mark_persistent(l_Std_Http_Server_instHandlerStatelessHandler);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server_Handler(
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
pub unsafe fn initialize_Std_Http_Server_Handler(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Async(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_ContextAsync(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Handler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server_Handler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Server_Handler(builtin);
}
