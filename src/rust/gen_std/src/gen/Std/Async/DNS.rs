// Lean compiler output
// Module: Std.Async.DNS
// Imports: Std.Time Std.Internal.UV Std.Async.Basic Init.Data.Function
use crate::ffi::{
    lean_io_promise_result_opt, lean_task_map, lean_uv_dns_get_info, lean_uv_dns_get_name,
};
use crate::r#gen::Init::Control::Except::l_Except_map;
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, l_Function_uncurry, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Std::Async::Basic::{
    initialize_Std_Async_Basic,
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    runtime_initialize_Std_Async_Basic,
};
use crate::r#gen::Std::Internal::UV::{
    initialize_Std_Internal_UV, runtime_initialize_Std_Internal_UV,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
pub static l_Std_Async_DNS_getAddrInfo___closed__0_value: leanh::LeanStringObject<44> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100,
            32, 116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 119, 97, 115, 32, 100,
            114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Async_DNS_getAddrInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getAddrInfo___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getAddrInfo___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getAddrInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getAddrInfo___closed__2_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getAddrInfo___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getAddrInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Async_DNS_getNameInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__1_value: leanh::LeanClosureObject<4> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_uncurry as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__2_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getNameInfo___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__3_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getNameInfo___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__4_value: leanh::LeanClosureObject<4> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__4_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__0(
    mut v___x_209_: *mut leanh::LeanObject,
    mut v_x_210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_211_ = lean_mk_io_user_error(v___x_209_);
        v___x_212_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_212_, 0, v___x_211_);
        return v___x_212_;
    } else {
        let mut v_val_213_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_209_);
        v_val_213_ = leanh::lean_ctor_get(v_x_210_, 0);
        leanh::lean_inc(v_val_213_);
        return v_val_213_;
    }
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__0___boxed(
    mut v___x_214_: *mut leanh::LeanObject,
    mut v_x_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_Async_DNS_getAddrInfo___lam__0(v___x_214_, v_x_215_);
    leanh::lean_dec(v_x_215_);
    return v_res_216_;
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__1(
    mut v___f_217_: *mut leanh::LeanObject,
    mut v_x_218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_223_: u8 = 0;
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_228_: u8 = 0;
    let mut v_a_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_238_: u8 = 0;
    let mut v_a_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: u8 = 0;
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_218_) == 0 {
                    leanh::lean_dec_ref(v___f_217_);
                    v_a_220_ = leanh::lean_ctor_get(v_x_218_, 0);
                    v_isSharedCheck_228_ = (!leanh::lean_is_exclusive(v_x_218_)) as u8;
                    if v_isSharedCheck_228_ == 0 {
                        v___x_222_ = v_x_218_;
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_220_);
                        leanh::lean_dec(v_x_218_);
                        v___x_222_ = leanh::lean_box(0);
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_229_ = leanh::lean_ctor_get(v_x_218_, 0);
                    leanh::lean_inc(v_a_229_);
                    leanh::lean_dec_ref_known(v_x_218_, 1);
                    if leanh::lean_obj_tag(v_a_229_) == 0 {
                        leanh::lean_dec_ref(v___f_217_);
                        v_a_230_ = leanh::lean_ctor_get(v_a_229_, 0);
                        v_isSharedCheck_238_ = (!leanh::lean_is_exclusive(v_a_229_)) as u8;
                        if v_isSharedCheck_238_ == 0 {
                            v___x_232_ = v_a_229_;
                            v_isShared_233_ = v_isSharedCheck_238_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_230_);
                            leanh::lean_dec(v_a_229_);
                            v___x_232_ = leanh::lean_box(0);
                            v_isShared_233_ = v_isSharedCheck_238_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_239_ = leanh::lean_ctor_get(v_a_229_, 0);
                        leanh::lean_inc(v_a_239_);
                        leanh::lean_dec_ref_known(v_a_229_, 1);
                        v___x_240_ = lean_io_promise_result_opt(v_a_239_);
                        leanh::lean_dec(v_a_239_);
                        v___x_241_ = leanh::lean_unsigned_to_nat(0);
                        v___x_242_ = 0;
                        v___x_243_ = lean_task_map(v___f_217_, v___x_240_, v___x_241_, v___x_242_);
                        v___x_244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_244_, 0, v___x_243_);
                        return v___x_244_;
                    }
                }
            }
            1 => {
                if v_isShared_223_ == 0 {
                    v___x_225_ = v___x_222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
                    v___x_225_ = v_reuseFailAlloc_227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
                return v___x_226_;
            }
            3 => {
                if v_isShared_233_ == 0 {
                    v___x_235_ = v___x_232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_230_);
                    v___x_235_ = v_reuseFailAlloc_237_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_236_, 0, v___x_235_);
                return v___x_236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__1___boxed(
    mut v___f_245_: *mut leanh::LeanObject,
    mut v_x_246_: *mut leanh::LeanObject,
    mut v___y_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Std_Async_DNS_getAddrInfo___lam__1(v___f_245_, v_x_246_);
    return v_res_248_;
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo(
    mut v_host_254_: *mut leanh::LeanObject,
    mut v_service_255_: *mut leanh::LeanObject,
    mut v_addrFamily_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: u8 = 0;
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_267_: u8 = 0;
    let mut v___f_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_273_: u8 = 0;
    let mut v___x_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_277_: u8 = 0;
    let mut v_a_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_285_: u8 = 0;
    let mut v___x_286_: u8 = 0;
    let mut v_val_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u8 = 0;
    let mut v___x_289_: u8 = 0;
    let mut v___x_290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_addrFamily_256_) == 0 {
                    v___x_286_ = 0;
                    v___y_267_ = v___x_286_;
                    state = 2;
                    continue;
                } else {
                    v_val_287_ = leanh::lean_ctor_get(v_addrFamily_256_, 0);
                    v___x_288_ = (leanh::lean_unbox(v_val_287_) as u8);
                    if v___x_288_ == 0 {
                        v___x_289_ = 1;
                        v___y_267_ = v___x_289_;
                        state = 2;
                        continue;
                    } else {
                        v___x_290_ = 2;
                        v___y_267_ = v___x_290_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_261_, 0, v_val_260_);
                v___x_262_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_262_, 0, v___x_261_);
                v___x_263_ = leanh::lean_unsigned_to_nat(0);
                v___x_264_ = 0;
                leanh::lean_inc_ref(v___y_259_);
                v___x_265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_263_,
                    v___x_264_,
                    v___x_262_,
                    v___y_259_,
                );
                return v___x_265_;
            }
            2 => {
                v___f_268_ = l_Std_Async_DNS_getAddrInfo___closed__2;
                v___x_269_ = lean_uv_dns_get_info(v_host_254_, v_service_255_, v___y_267_);
                if leanh::lean_obj_tag(v___x_269_) == 0 {
                    v_a_270_ = leanh::lean_ctor_get(v___x_269_, 0);
                    v_isSharedCheck_277_ = (!leanh::lean_is_exclusive(v___x_269_)) as u8;
                    if v_isSharedCheck_277_ == 0 {
                        v___x_272_ = v___x_269_;
                        v_isShared_273_ = v_isSharedCheck_277_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_270_);
                        leanh::lean_dec(v___x_269_);
                        v___x_272_ = leanh::lean_box(0);
                        v_isShared_273_ = v_isSharedCheck_277_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_278_ = leanh::lean_ctor_get(v___x_269_, 0);
                    v_isSharedCheck_285_ = (!leanh::lean_is_exclusive(v___x_269_)) as u8;
                    if v_isSharedCheck_285_ == 0 {
                        v___x_280_ = v___x_269_;
                        v_isShared_281_ = v_isSharedCheck_285_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_278_);
                        leanh::lean_dec(v___x_269_);
                        v___x_280_ = leanh::lean_box(0);
                        v_isShared_281_ = v_isSharedCheck_285_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_273_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_272_, 1);
                    v___x_275_ = v___x_272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
                    v___x_275_ = v_reuseFailAlloc_276_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_259_ = v___f_268_;
                v_val_260_ = v___x_275_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_281_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_280_, 0);
                    v___x_283_ = v___x_280_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
                    v___x_283_ = v_reuseFailAlloc_284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_259_ = v___f_268_;
                v_val_260_ = v___x_283_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___boxed(
    mut v_host_291_: *mut leanh::LeanObject,
    mut v_service_292_: *mut leanh::LeanObject,
    mut v_addrFamily_293_: *mut leanh::LeanObject,
    mut v_a_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Std_Async_DNS_getAddrInfo(v_host_291_, v_service_292_, v_addrFamily_293_);
    leanh::lean_dec(v_addrFamily_293_);
    leanh::lean_dec_ref(v_service_292_);
    leanh::lean_dec_ref(v_host_291_);
    return v_res_295_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__0(
    mut v_host_296_: *mut leanh::LeanObject,
    mut v_service_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_298_, 0, v_host_296_);
    leanh::lean_ctor_set(v___x_298_, 1, v_service_297_);
    return v___x_298_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__1(
    mut v___x_299_: *mut leanh::LeanObject,
    mut v_x_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_300_) == 0 {
        let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_301_ = lean_mk_io_user_error(v___x_299_);
        v___x_302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_302_, 0, v___x_301_);
        return v___x_302_;
    } else {
        let mut v_val_303_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_299_);
        v_val_303_ = leanh::lean_ctor_get(v_x_300_, 0);
        leanh::lean_inc(v_val_303_);
        return v_val_303_;
    }
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__1___boxed(
    mut v___x_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l_Std_Async_DNS_getNameInfo___lam__1(v___x_304_, v_x_305_);
    leanh::lean_dec(v_x_305_);
    return v_res_306_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__2(
    mut v___f_307_: *mut leanh::LeanObject,
    mut v_x_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_313_: u8 = 0;
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_318_: u8 = 0;
    let mut v_a_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_323_: u8 = 0;
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_328_: u8 = 0;
    let mut v_a_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_308_) == 0 {
                    leanh::lean_dec_ref(v___f_307_);
                    v_a_310_ = leanh::lean_ctor_get(v_x_308_, 0);
                    v_isSharedCheck_318_ = (!leanh::lean_is_exclusive(v_x_308_)) as u8;
                    if v_isSharedCheck_318_ == 0 {
                        v___x_312_ = v_x_308_;
                        v_isShared_313_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_310_);
                        leanh::lean_dec(v_x_308_);
                        v___x_312_ = leanh::lean_box(0);
                        v_isShared_313_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_319_ = leanh::lean_ctor_get(v_x_308_, 0);
                    leanh::lean_inc(v_a_319_);
                    leanh::lean_dec_ref_known(v_x_308_, 1);
                    if leanh::lean_obj_tag(v_a_319_) == 0 {
                        leanh::lean_dec_ref(v___f_307_);
                        v_a_320_ = leanh::lean_ctor_get(v_a_319_, 0);
                        v_isSharedCheck_328_ = (!leanh::lean_is_exclusive(v_a_319_)) as u8;
                        if v_isSharedCheck_328_ == 0 {
                            v___x_322_ = v_a_319_;
                            v_isShared_323_ = v_isSharedCheck_328_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_320_);
                            leanh::lean_dec(v_a_319_);
                            v___x_322_ = leanh::lean_box(0);
                            v_isShared_323_ = v_isSharedCheck_328_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_329_ = leanh::lean_ctor_get(v_a_319_, 0);
                        leanh::lean_inc(v_a_329_);
                        leanh::lean_dec_ref_known(v_a_319_, 1);
                        v___x_330_ = lean_io_promise_result_opt(v_a_329_);
                        leanh::lean_dec(v_a_329_);
                        v___x_331_ = leanh::lean_unsigned_to_nat(0);
                        v___x_332_ = 0;
                        v___x_333_ = lean_task_map(v___f_307_, v___x_330_, v___x_331_, v___x_332_);
                        v___x_334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_334_, 0, v___x_333_);
                        return v___x_334_;
                    }
                }
            }
            1 => {
                if v_isShared_313_ == 0 {
                    v___x_315_ = v___x_312_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_310_);
                    v___x_315_ = v_reuseFailAlloc_317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_316_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_316_, 0, v___x_315_);
                return v___x_316_;
            }
            3 => {
                if v_isShared_323_ == 0 {
                    v___x_325_ = v___x_322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_320_);
                    v___x_325_ = v_reuseFailAlloc_327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_326_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_326_, 0, v___x_325_);
                return v___x_326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__2___boxed(
    mut v___f_335_: *mut leanh::LeanObject,
    mut v_x_336_: *mut leanh::LeanObject,
    mut v___y_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_338_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_335_, v_x_336_);
    return v_res_338_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo(
    mut v_host_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: u8 = 0;
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_365_: u8 = 0;
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_369_: u8 = 0;
    let mut v_a_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v_fst_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_378_: u8 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_385_: u8 = 0;
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_a_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_390_: u8 = 0;
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_396_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut v_a_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_409_: u8 = 0;
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_353_ = l_Std_Async_DNS_getNameInfo___closed__3;
                v___x_397_ = lean_uv_dns_get_name(v_host_348_);
                if leanh::lean_obj_tag(v___x_397_) == 0 {
                    v_a_398_ = leanh::lean_ctor_get(v___x_397_, 0);
                    v_isSharedCheck_405_ = (!leanh::lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_405_ == 0 {
                        v___x_400_ = v___x_397_;
                        v_isShared_401_ = v_isSharedCheck_405_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_398_);
                        leanh::lean_dec(v___x_397_);
                        v___x_400_ = leanh::lean_box(0);
                        v_isShared_401_ = v_isSharedCheck_405_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_a_406_ = leanh::lean_ctor_get(v___x_397_, 0);
                    v_isSharedCheck_413_ = (!leanh::lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_413_ == 0 {
                        v___x_408_ = v___x_397_;
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_406_);
                        leanh::lean_dec(v___x_397_);
                        v___x_408_ = leanh::lean_box(0);
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_352_, 0, v___y_351_);
                return v___x_352_;
            }
            2 => {
                v___x_356_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_356_, 0, v_val_355_);
                v___x_357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_357_, 0, v___x_356_);
                v___x_358_ = leanh::lean_unsigned_to_nat(0);
                v___x_359_ = 0;
                v___x_360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_358_,
                    v___x_359_,
                    v___x_357_,
                    v___f_353_,
                );
                if leanh::lean_obj_tag(v___x_360_) == 0 {
                    v_a_361_ = leanh::lean_ctor_get(v___x_360_, 0);
                    leanh::lean_inc(v_a_361_);
                    leanh::lean_dec_ref_known(v___x_360_, 1);
                    if leanh::lean_obj_tag(v_a_361_) == 0 {
                        v_a_362_ = leanh::lean_ctor_get(v_a_361_, 0);
                        v_isSharedCheck_369_ = (!leanh::lean_is_exclusive(v_a_361_)) as u8;
                        if v_isSharedCheck_369_ == 0 {
                            v___x_364_ = v_a_361_;
                            v_isShared_365_ = v_isSharedCheck_369_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_362_);
                            leanh::lean_dec(v_a_361_);
                            v___x_364_ = leanh::lean_box(0);
                            v_isShared_365_ = v_isSharedCheck_369_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_370_ = leanh::lean_ctor_get(v_a_361_, 0);
                        v_isSharedCheck_386_ = (!leanh::lean_is_exclusive(v_a_361_)) as u8;
                        if v_isSharedCheck_386_ == 0 {
                            v___x_372_ = v_a_361_;
                            v_isShared_373_ = v_isSharedCheck_386_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_370_);
                            leanh::lean_dec(v_a_361_);
                            v___x_372_ = leanh::lean_box(0);
                            v_isShared_373_ = v_isSharedCheck_386_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_387_ = leanh::lean_ctor_get(v___x_360_, 0);
                    v_isSharedCheck_396_ = (!leanh::lean_is_exclusive(v___x_360_)) as u8;
                    if v_isSharedCheck_396_ == 0 {
                        v___x_389_ = v___x_360_;
                        v_isShared_390_ = v_isSharedCheck_396_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_387_);
                        leanh::lean_dec(v___x_360_);
                        v___x_389_ = leanh::lean_box(0);
                        v_isShared_390_ = v_isSharedCheck_396_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_365_ == 0 {
                    v___x_367_ = v___x_364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_368_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
                    v___x_367_ = v_reuseFailAlloc_368_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_351_ = v___x_367_;
                state = 1;
                continue;
            }
            5 => {
                v_fst_374_ = leanh::lean_ctor_get(v_a_370_, 0);
                v_snd_375_ = leanh::lean_ctor_get(v_a_370_, 1);
                v_isSharedCheck_385_ = (!leanh::lean_is_exclusive(v_a_370_)) as u8;
                if v_isSharedCheck_385_ == 0 {
                    v___x_377_ = v_a_370_;
                    v_isShared_378_ = v_isSharedCheck_385_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_375_);
                    leanh::lean_inc(v_fst_374_);
                    leanh::lean_dec(v_a_370_);
                    v___x_377_ = leanh::lean_box(0);
                    v_isShared_378_ = v_isSharedCheck_385_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_378_ == 0 {
                    v___x_380_ = v___x_377_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_384_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_384_, 0, v_fst_374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_384_, 1, v_snd_375_);
                    v___x_380_ = v_reuseFailAlloc_384_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_373_ == 0 {
                    leanh::lean_ctor_set(v___x_372_, 0, v___x_380_);
                    v___x_382_ = v___x_372_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
                    v___x_382_ = v_reuseFailAlloc_383_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_351_ = v___x_382_;
                state = 1;
                continue;
            }
            9 => {
                v___x_391_ = l_Std_Async_DNS_getNameInfo___closed__4;
                v___x_392_ = lean_task_map(v___x_391_, v_a_387_, v___x_358_, v___x_359_);
                if v_isShared_390_ == 0 {
                    leanh::lean_ctor_set(v___x_389_, 0, v___x_392_);
                    v___x_394_ = v___x_389_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
                    v___x_394_ = v_reuseFailAlloc_395_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_394_;
            }
            11 => {
                if v_isShared_401_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_400_, 1);
                    v___x_403_ = v___x_400_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
                    v___x_403_ = v_reuseFailAlloc_404_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_val_355_ = v___x_403_;
                state = 2;
                continue;
            }
            13 => {
                if v_isShared_409_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_408_, 0);
                    v___x_411_ = v___x_408_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
                    v___x_411_ = v_reuseFailAlloc_412_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_val_355_ = v___x_411_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___boxed(
    mut v_host_414_: *mut leanh::LeanObject,
    mut v_a_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Async_DNS_getNameInfo(v_host_414_);
    leanh::lean_dec_ref(v_host_414_);
    return v_res_416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_DNS(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_DNS(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_DNS(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_DNS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_DNS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Async_DNS(builtin);
}