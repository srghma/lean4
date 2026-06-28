// Lean compiler output
// Module: Std.Async.DNS
// Imports: Std.Time Std.Internal.UV Std.Async.Basic Init.Data.Function
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
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::System::Promise::lean_io_promise_result_opt;
use crate::lean_imports_rs::Std::Internal::UV::DNS::{lean_uv_dns_get_info, lean_uv_dns_get_name};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Std_Async_DNS_getAddrInfo___closed__0_value: LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100, 32,
        116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 119, 97, 115, 32, 100, 114,
        111, 112, 112, 101, 100, 0,
    ],
};
static mut l_Std_Async_DNS_getAddrInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getAddrInfo___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getAddrInfo___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getAddrInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getAddrInfo___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getAddrInfo___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__1_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getAddrInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getNameInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__1_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_uncurry as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__2_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getNameInfo___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getAddrInfo___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__3_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_DNS_getNameInfo___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__3_value) as *mut LeanObject;
pub static l_Std_Async_DNS_getNameInfo___closed__4_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__1_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_DNS_getNameInfo___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_DNS_getNameInfo___closed__4_value) as *mut LeanObject;
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__0(
    mut v___x_209_: *mut LeanObject,
    mut v_x_210_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_210_) == 0 {
        let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
        v___x_211_ = lean_mk_io_user_error(v___x_209_);
        v___x_212_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_212_, 0, v___x_211_);
        return v___x_212_;
    } else {
        let mut v_val_213_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_209_);
        v_val_213_ = lean_ctor_get(v_x_210_, 0);
        lean_inc(v_val_213_);
        return v_val_213_;
    }
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__0___boxed(
    mut v___x_214_: *mut LeanObject,
    mut v_x_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_Async_DNS_getAddrInfo___lam__0(v___x_214_, v_x_215_);
    lean_dec(v_x_215_);
    return v_res_216_;
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__1(
    mut v___f_217_: *mut LeanObject,
    mut v_x_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_223_: u8 = 0;
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_228_: u8 = 0;
    let mut v_a_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_238_: u8 = 0;
    let mut v_a_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: u8 = 0;
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_218_) == 0 {
                    lean_dec_ref(v___f_217_);
                    v_a_220_ = lean_ctor_get(v_x_218_, 0);
                    v_isSharedCheck_228_ = (!lean_is_exclusive(v_x_218_)) as u8;
                    if v_isSharedCheck_228_ == 0 {
                        v___x_222_ = v_x_218_;
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_220_);
                        lean_dec(v_x_218_);
                        v___x_222_ = lean_box(0);
                        v_isShared_223_ = v_isSharedCheck_228_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_229_ = lean_ctor_get(v_x_218_, 0);
                    lean_inc(v_a_229_);
                    lean_dec_ref_known(v_x_218_, 1);
                    if lean_obj_tag(v_a_229_) == 0 {
                        lean_dec_ref(v___f_217_);
                        v_a_230_ = lean_ctor_get(v_a_229_, 0);
                        v_isSharedCheck_238_ = (!lean_is_exclusive(v_a_229_)) as u8;
                        if v_isSharedCheck_238_ == 0 {
                            v___x_232_ = v_a_229_;
                            v_isShared_233_ = v_isSharedCheck_238_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_230_);
                            lean_dec(v_a_229_);
                            v___x_232_ = lean_box(0);
                            v_isShared_233_ = v_isSharedCheck_238_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_239_ = lean_ctor_get(v_a_229_, 0);
                        lean_inc(v_a_239_);
                        lean_dec_ref_known(v_a_229_, 1);
                        v___x_240_ = lean_io_promise_result_opt(v_a_239_);
                        lean_dec(v_a_239_);
                        v___x_241_ = lean_unsigned_to_nat(0);
                        v___x_242_ = 0;
                        v___x_243_ = lean_task_map(v___f_217_, v___x_240_, v___x_241_, v___x_242_);
                        v___x_244_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_244_, 0, v___x_243_);
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
                    v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_220_);
                    v___x_225_ = v_reuseFailAlloc_227_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_226_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_226_, 0, v___x_225_);
                return v___x_226_;
            }
            3 => {
                if v_isShared_233_ == 0 {
                    v___x_235_ = v___x_232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_230_);
                    v___x_235_ = v_reuseFailAlloc_237_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_236_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_236_, 0, v___x_235_);
                return v___x_236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo___lam__1___boxed(
    mut v___f_245_: *mut LeanObject,
    mut v_x_246_: *mut LeanObject,
    mut v___y_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_248_: *mut LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Std_Async_DNS_getAddrInfo___lam__1(v___f_245_, v_x_246_);
    return v_res_248_;
}
pub unsafe fn l_Std_Async_DNS_getAddrInfo(
    mut v_host_254_: *mut LeanObject,
    mut v_service_255_: *mut LeanObject,
    mut v_addrFamily_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: u8 = 0;
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_267_: u8 = 0;
    let mut v___f_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_273_: u8 = 0;
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_277_: u8 = 0;
    let mut v_a_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_285_: u8 = 0;
    let mut v___x_286_: u8 = 0;
    let mut v_val_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u8 = 0;
    let mut v___x_289_: u8 = 0;
    let mut v___x_290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_addrFamily_256_) == 0 {
                    v___x_286_ = 0;
                    v___y_267_ = v___x_286_;
                    state = 2;
                    continue;
                } else {
                    v_val_287_ = lean_ctor_get(v_addrFamily_256_, 0);
                    v___x_288_ = (lean_unbox(v_val_287_) as u8);
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
                v___x_261_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_261_, 0, v_val_260_);
                v___x_262_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_262_, 0, v___x_261_);
                v___x_263_ = lean_unsigned_to_nat(0);
                v___x_264_ = 0;
                lean_inc_ref(v___y_259_);
                v___x_265_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                if lean_obj_tag(v___x_269_) == 0 {
                    v_a_270_ = lean_ctor_get(v___x_269_, 0);
                    v_isSharedCheck_277_ = (!lean_is_exclusive(v___x_269_)) as u8;
                    if v_isSharedCheck_277_ == 0 {
                        v___x_272_ = v___x_269_;
                        v_isShared_273_ = v_isSharedCheck_277_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_270_);
                        lean_dec(v___x_269_);
                        v___x_272_ = lean_box(0);
                        v_isShared_273_ = v_isSharedCheck_277_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_278_ = lean_ctor_get(v___x_269_, 0);
                    v_isSharedCheck_285_ = (!lean_is_exclusive(v___x_269_)) as u8;
                    if v_isSharedCheck_285_ == 0 {
                        v___x_280_ = v___x_269_;
                        v_isShared_281_ = v_isSharedCheck_285_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_278_);
                        lean_dec(v___x_269_);
                        v___x_280_ = lean_box(0);
                        v_isShared_281_ = v_isSharedCheck_285_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_273_ == 0 {
                    lean_ctor_set_tag(v___x_272_, 1);
                    v___x_275_ = v___x_272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
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
                    lean_ctor_set_tag(v___x_280_, 0);
                    v___x_283_ = v___x_280_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
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
    mut v_host_291_: *mut LeanObject,
    mut v_service_292_: *mut LeanObject,
    mut v_addrFamily_293_: *mut LeanObject,
    mut v_a_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Std_Async_DNS_getAddrInfo(v_host_291_, v_service_292_, v_addrFamily_293_);
    lean_dec(v_addrFamily_293_);
    lean_dec_ref(v_service_292_);
    lean_dec_ref(v_host_291_);
    return v_res_295_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__0(
    mut v_host_296_: *mut LeanObject,
    mut v_service_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_298_, 0, v_host_296_);
    lean_ctor_set(v___x_298_, 1, v_service_297_);
    return v___x_298_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__1(
    mut v___x_299_: *mut LeanObject,
    mut v_x_300_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_300_) == 0 {
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
        v___x_301_ = lean_mk_io_user_error(v___x_299_);
        v___x_302_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_302_, 0, v___x_301_);
        return v___x_302_;
    } else {
        let mut v_val_303_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_299_);
        v_val_303_ = lean_ctor_get(v_x_300_, 0);
        lean_inc(v_val_303_);
        return v_val_303_;
    }
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__1___boxed(
    mut v___x_304_: *mut LeanObject,
    mut v_x_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = l_Std_Async_DNS_getNameInfo___lam__1(v___x_304_, v_x_305_);
    lean_dec(v_x_305_);
    return v_res_306_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__2(
    mut v___f_307_: *mut LeanObject,
    mut v_x_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_313_: u8 = 0;
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_318_: u8 = 0;
    let mut v_a_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_323_: u8 = 0;
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_328_: u8 = 0;
    let mut v_a_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_308_) == 0 {
                    lean_dec_ref(v___f_307_);
                    v_a_310_ = lean_ctor_get(v_x_308_, 0);
                    v_isSharedCheck_318_ = (!lean_is_exclusive(v_x_308_)) as u8;
                    if v_isSharedCheck_318_ == 0 {
                        v___x_312_ = v_x_308_;
                        v_isShared_313_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_310_);
                        lean_dec(v_x_308_);
                        v___x_312_ = lean_box(0);
                        v_isShared_313_ = v_isSharedCheck_318_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_319_ = lean_ctor_get(v_x_308_, 0);
                    lean_inc(v_a_319_);
                    lean_dec_ref_known(v_x_308_, 1);
                    if lean_obj_tag(v_a_319_) == 0 {
                        lean_dec_ref(v___f_307_);
                        v_a_320_ = lean_ctor_get(v_a_319_, 0);
                        v_isSharedCheck_328_ = (!lean_is_exclusive(v_a_319_)) as u8;
                        if v_isSharedCheck_328_ == 0 {
                            v___x_322_ = v_a_319_;
                            v_isShared_323_ = v_isSharedCheck_328_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_320_);
                            lean_dec(v_a_319_);
                            v___x_322_ = lean_box(0);
                            v_isShared_323_ = v_isSharedCheck_328_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_329_ = lean_ctor_get(v_a_319_, 0);
                        lean_inc(v_a_329_);
                        lean_dec_ref_known(v_a_319_, 1);
                        v___x_330_ = lean_io_promise_result_opt(v_a_329_);
                        lean_dec(v_a_329_);
                        v___x_331_ = lean_unsigned_to_nat(0);
                        v___x_332_ = 0;
                        v___x_333_ = lean_task_map(v___f_307_, v___x_330_, v___x_331_, v___x_332_);
                        v___x_334_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_334_, 0, v___x_333_);
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
                    v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_310_);
                    v___x_315_ = v_reuseFailAlloc_317_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_316_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_316_, 0, v___x_315_);
                return v___x_316_;
            }
            3 => {
                if v_isShared_323_ == 0 {
                    v___x_325_ = v___x_322_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_320_);
                    v___x_325_ = v_reuseFailAlloc_327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_326_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_326_, 0, v___x_325_);
                return v___x_326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_DNS_getNameInfo___lam__2___boxed(
    mut v___f_335_: *mut LeanObject,
    mut v_x_336_: *mut LeanObject,
    mut v___y_337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_338_: *mut LeanObject = core::ptr::null_mut();
    v_res_338_ = l_Std_Async_DNS_getNameInfo___lam__2(v___f_335_, v_x_336_);
    return v_res_338_;
}
pub unsafe fn l_Std_Async_DNS_getNameInfo(mut v_host_348_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: u8 = 0;
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_365_: u8 = 0;
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_369_: u8 = 0;
    let mut v_a_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v_fst_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_378_: u8 = 0;
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_385_: u8 = 0;
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut v_a_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_390_: u8 = 0;
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_396_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut v_a_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_409_: u8 = 0;
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_353_ = l_Std_Async_DNS_getNameInfo___closed__3;
                v___x_397_ = lean_uv_dns_get_name(v_host_348_);
                if lean_obj_tag(v___x_397_) == 0 {
                    v_a_398_ = lean_ctor_get(v___x_397_, 0);
                    v_isSharedCheck_405_ = (!lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_405_ == 0 {
                        v___x_400_ = v___x_397_;
                        v_isShared_401_ = v_isSharedCheck_405_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_398_);
                        lean_dec(v___x_397_);
                        v___x_400_ = lean_box(0);
                        v_isShared_401_ = v_isSharedCheck_405_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_a_406_ = lean_ctor_get(v___x_397_, 0);
                    v_isSharedCheck_413_ = (!lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_413_ == 0 {
                        v___x_408_ = v___x_397_;
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_406_);
                        lean_dec(v___x_397_);
                        v___x_408_ = lean_box(0);
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_352_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_352_, 0, v___y_351_);
                return v___x_352_;
            }
            2 => {
                v___x_356_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_356_, 0, v_val_355_);
                v___x_357_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_357_, 0, v___x_356_);
                v___x_358_ = lean_unsigned_to_nat(0);
                v___x_359_ = 0;
                v___x_360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_358_,
                    v___x_359_,
                    v___x_357_,
                    v___f_353_,
                );
                if lean_obj_tag(v___x_360_) == 0 {
                    v_a_361_ = lean_ctor_get(v___x_360_, 0);
                    lean_inc(v_a_361_);
                    lean_dec_ref_known(v___x_360_, 1);
                    if lean_obj_tag(v_a_361_) == 0 {
                        v_a_362_ = lean_ctor_get(v_a_361_, 0);
                        v_isSharedCheck_369_ = (!lean_is_exclusive(v_a_361_)) as u8;
                        if v_isSharedCheck_369_ == 0 {
                            v___x_364_ = v_a_361_;
                            v_isShared_365_ = v_isSharedCheck_369_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_362_);
                            lean_dec(v_a_361_);
                            v___x_364_ = lean_box(0);
                            v_isShared_365_ = v_isSharedCheck_369_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_370_ = lean_ctor_get(v_a_361_, 0);
                        v_isSharedCheck_386_ = (!lean_is_exclusive(v_a_361_)) as u8;
                        if v_isSharedCheck_386_ == 0 {
                            v___x_372_ = v_a_361_;
                            v_isShared_373_ = v_isSharedCheck_386_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_370_);
                            lean_dec(v_a_361_);
                            v___x_372_ = lean_box(0);
                            v_isShared_373_ = v_isSharedCheck_386_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_387_ = lean_ctor_get(v___x_360_, 0);
                    v_isSharedCheck_396_ = (!lean_is_exclusive(v___x_360_)) as u8;
                    if v_isSharedCheck_396_ == 0 {
                        v___x_389_ = v___x_360_;
                        v_isShared_390_ = v_isSharedCheck_396_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_387_);
                        lean_dec(v___x_360_);
                        v___x_389_ = lean_box(0);
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
                    v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
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
                v_fst_374_ = lean_ctor_get(v_a_370_, 0);
                v_snd_375_ = lean_ctor_get(v_a_370_, 1);
                v_isSharedCheck_385_ = (!lean_is_exclusive(v_a_370_)) as u8;
                if v_isSharedCheck_385_ == 0 {
                    v___x_377_ = v_a_370_;
                    v_isShared_378_ = v_isSharedCheck_385_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_375_);
                    lean_inc(v_fst_374_);
                    lean_dec(v_a_370_);
                    v___x_377_ = lean_box(0);
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
                    v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_384_, 0, v_fst_374_);
                    lean_ctor_set(v_reuseFailAlloc_384_, 1, v_snd_375_);
                    v___x_380_ = v_reuseFailAlloc_384_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_373_ == 0 {
                    lean_ctor_set(v___x_372_, 0, v___x_380_);
                    v___x_382_ = v___x_372_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
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
                    lean_ctor_set(v___x_389_, 0, v___x_392_);
                    v___x_394_ = v___x_389_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
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
                    lean_ctor_set_tag(v___x_400_, 1);
                    v___x_403_ = v___x_400_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
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
                    lean_ctor_set_tag(v___x_408_, 0);
                    v___x_411_ = v___x_408_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
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
    mut v_host_414_: *mut LeanObject,
    mut v_a_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Async_DNS_getNameInfo(v_host_414_);
    lean_dec_ref(v_host_414_);
    return v_res_416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_DNS(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Internal_UV(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_DNS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_DNS(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Std_Internal_UV(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_DNS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_DNS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_DNS(builtin);
}
