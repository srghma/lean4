// Lean compiler output
// Module: Lean.Server.RequestCancellation
// Imports: Lean.Server.ServerTask Init.System.Promise Init.System.CancelToken
use crate::ffi::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt, lean_task_map,
};
use crate::r#gen::Init::Control::Except::l_ExceptT_bindCont;
use crate::r#gen::Init::System::CancelToken::{
    initialize_Init_System_CancelToken, l_IO_CancelToken_isSet, l_IO_CancelToken_new,
    l_IO_CancelToken_set, runtime_initialize_Init_System_CancelToken,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Lean::Server::ServerTask::{
    initialize_Lean_Server_ServerTask, runtime_initialize_Lean_Server_ServerTask,
};
pub static l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value:
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
    m_fun: l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Server_RequestCancellation_requestCancelled: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
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
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value:
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
    m_fun: l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Server_RequestCancellationToken_new() -> *mut leanh::LeanObject {
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = l_IO_CancelToken_new();
    v___x_217_ = l_IO_CancelToken_new();
    v___x_218_ = lean_io_promise_new();
    v___x_219_ = lean_io_promise_new();
    v___x_220_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_220_, 0, v___x_216_);
    leanh::lean_ctor_set(v___x_220_, 1, v___x_217_);
    leanh::lean_ctor_set(v___x_220_, 2, v___x_218_);
    leanh::lean_ctor_set(v___x_220_, 3, v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_new___boxed(
    mut v_a_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_Server_RequestCancellationToken_new();
    return v_res_222_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(
    mut v_tk_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cancelledByCancelRequest_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_requestCancellationPromise_226_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cancelledByCancelRequest_225_ = leanh::lean_ctor_get(v_tk_223_, 0);
    v_requestCancellationPromise_226_ = leanh::lean_ctor_get(v_tk_223_, 2);
    v___x_227_ = l_IO_CancelToken_set(v_cancelledByCancelRequest_225_);
    v___x_228_ = leanh::lean_box(0);
    v___x_229_ = lean_io_promise_resolve(v___x_228_, v_requestCancellationPromise_226_);
    return v___x_229_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(
    mut v_tk_230_: *mut leanh::LeanObject,
    mut v_a_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_232_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_230_);
    leanh::lean_dec_ref(v_tk_230_);
    return v_res_232_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByEdit(
    mut v_tk_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cancelledByEdit_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_editCancellationPromise_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cancelledByEdit_235_ = leanh::lean_ctor_get(v_tk_233_, 1);
    v_editCancellationPromise_236_ = leanh::lean_ctor_get(v_tk_233_, 3);
    v___x_237_ = l_IO_CancelToken_set(v_cancelledByEdit_235_);
    v___x_238_ = leanh::lean_box(0);
    v___x_239_ = lean_io_promise_resolve(v___x_238_, v_editCancellationPromise_236_);
    return v___x_239_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(
    mut v_tk_240_: *mut leanh::LeanObject,
    mut v_a_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_240_);
    leanh::lean_dec_ref(v_tk_240_);
    return v_res_242_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(
    mut v_x_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_243_) == 0 {
        let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_244_ = leanh::lean_box(0);
        return v___x_244_;
    } else {
        let mut v_val_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_245_ = leanh::lean_ctor_get(v_x_243_, 0);
        leanh::lean_inc(v_val_245_);
        return v_val_245_;
    }
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(
    mut v_x_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(v_x_246_);
    leanh::lean_dec(v_x_246_);
    return v_res_247_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask(
    mut v_tk_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_requestCancellationPromise_250_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v___f_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: u8 = 0;
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_requestCancellationPromise_250_ = leanh::lean_ctor_get(v_tk_249_, 2);
    v___f_251_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0;
    v___x_252_ = lean_io_promise_result_opt(v_requestCancellationPromise_250_);
    v___x_253_ = leanh::lean_unsigned_to_nat(0);
    v___x_254_ = 1;
    v___x_255_ = lean_task_map(v___f_251_, v___x_252_, v___x_253_, v___x_254_);
    return v___x_255_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(
    mut v_tk_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_256_);
    leanh::lean_dec_ref(v_tk_256_);
    return v_res_257_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_editCancellationTask(
    mut v_tk_258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_editCancellationPromise_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_editCancellationPromise_259_ = leanh::lean_ctor_get(v_tk_258_, 3);
    v___f_260_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0;
    v___x_261_ = lean_io_promise_result_opt(v_editCancellationPromise_259_);
    v___x_262_ = leanh::lean_unsigned_to_nat(0);
    v___x_263_ = 1;
    v___x_264_ = lean_task_map(v___f_260_, v___x_261_, v___x_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(
    mut v_tk_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_265_);
    leanh::lean_dec_ref(v_tk_265_);
    return v_res_266_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancellationTasks(
    mut v_tk_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_267_);
    v___x_269_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_267_);
    v___x_270_ = leanh::lean_box(0);
    v___x_271_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_271_, 0, v___x_269_);
    leanh::lean_ctor_set(v___x_271_, 1, v___x_270_);
    v___x_272_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_272_, 0, v___x_268_);
    leanh::lean_ctor_set(v___x_272_, 1, v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(
    mut v_tk_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_tk_273_);
    leanh::lean_dec_ref(v_tk_273_);
    return v_res_274_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(
    mut v_tk_275_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_cancelledByCancelRequest_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: u8 = 0;
    v_cancelledByCancelRequest_277_ = leanh::lean_ctor_get(v_tk_275_, 0);
    v___x_278_ = l_IO_CancelToken_isSet(v_cancelledByCancelRequest_277_);
    return v___x_278_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(
    mut v_tk_279_: *mut leanh::LeanObject,
    mut v_a_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_279_);
    leanh::lean_dec_ref(v_tk_279_);
    v_r_282_ = leanh::lean_box((v_res_281_) as usize);
    return v_r_282_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(
    mut v_tk_283_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_cancelledByEdit_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    v_cancelledByEdit_285_ = leanh::lean_ctor_get(v_tk_283_, 1);
    v___x_286_ = l_IO_CancelToken_isSet(v_cancelledByEdit_285_);
    return v___x_286_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(
    mut v_tk_287_: *mut leanh::LeanObject,
    mut v_a_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_289_: u8 = 0;
    let mut v_r_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_287_);
    leanh::lean_dec_ref(v_tk_287_);
    v_r_290_ = leanh::lean_box((v_res_289_) as usize);
    return v_r_290_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelled(
    mut v_tk_291_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_293_: u8 = 0;
    let mut v___x_294_: u8 = 0;
    v___x_293_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_291_);
    v___x_294_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_291_);
    if v___x_293_ == 0 {
        return v___x_294_;
    } else {
        return v___x_293_;
    }
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelled___boxed(
    mut v_tk_295_: *mut leanh::LeanObject,
    mut v_a_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_297_: u8 = 0;
    let mut v_r_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_295_);
    leanh::lean_dec_ref(v_tk_295_);
    v_r_298_ = leanh::lean_box((v_res_297_) as usize);
    return v_r_298_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_toCtorIdx(
    mut v_x_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = leanh::lean_unsigned_to_nat(0);
    return v___x_300_;
}
pub unsafe fn _init_l_Lean_Server_RequestCancellation_requestCancelled()
-> *mut leanh::LeanObject {
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = leanh::lean_box(0);
    return v___x_301_;
}
pub unsafe fn l_Lean_Server_CancellableT_run___redArg(
    mut v_tk_302_: *mut leanh::LeanObject,
    mut v_x_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_304_ = leanh::lean_apply_1(v_x_303_, v_tk_302_);
    return v___x_304_;
}
pub unsafe fn l_Lean_Server_CancellableT_run(
    mut v_m_305_: *mut leanh::LeanObject,
    mut v_00_u03b1_306_: *mut leanh::LeanObject,
    mut v_tk_307_: *mut leanh::LeanObject,
    mut v_x_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = leanh::lean_apply_1(v_x_308_, v_tk_307_);
    return v___x_309_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___redArg(
    mut v_tk_310_: *mut leanh::LeanObject,
    mut v_x_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_313_ = leanh::lean_apply_2(v_x_311_, v_tk_310_, leanh::lean_box(0));
    return v___x_313_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___redArg___boxed(
    mut v_tk_314_: *mut leanh::LeanObject,
    mut v_x_315_: *mut leanh::LeanObject,
    mut v_a_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Lean_Server_CancellableM_run___redArg(v_tk_314_, v_x_315_);
    return v_res_317_;
}
pub unsafe fn l_Lean_Server_CancellableM_run(
    mut v_00_u03b1_318_: *mut leanh::LeanObject,
    mut v_tk_319_: *mut leanh::LeanObject,
    mut v_x_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = leanh::lean_apply_2(v_x_320_, v_tk_319_, leanh::lean_box(0));
    return v___x_322_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___boxed(
    mut v_00_u03b1_323_: *mut leanh::LeanObject,
    mut v_tk_324_: *mut leanh::LeanObject,
    mut v_x_325_: *mut leanh::LeanObject,
    mut v_a_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Lean_Server_CancellableM_run(v_00_u03b1_323_, v_tk_324_, v_x_325_);
    return v_res_327_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(
    mut v_a_328_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = leanh::lean_box((v_a_328_) as usize);
    v___x_330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_330_, 0, v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(
    mut v_a_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_668__boxed_332_: u8 = 0;
    let mut v_res_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_668__boxed_332_ = (leanh::lean_unbox(v_a_331_) as u8);
    v_res_333_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_668__boxed_332_);
    return v_res_333_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(
    mut v_toPure_338_: *mut leanh::LeanObject,
    mut v_a_339_: u8,
) -> *mut leanh::LeanObject {
    if v_a_339_ == 0 {
        let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_340_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
        v___x_341_ =
            leanh::lean_apply_2(v_toPure_338_, leanh::lean_box(0), v___x_340_);
        return v___x_341_;
    } else {
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_342_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
        v___x_343_ =
            leanh::lean_apply_2(v_toPure_338_, leanh::lean_box(0), v___x_342_);
        return v___x_343_;
    }
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(
    mut v_toPure_344_: *mut leanh::LeanObject,
    mut v_a_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_346_: u8 = 0;
    let mut v_res_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_346_ = (leanh::lean_unbox(v_a_345_) as u8);
    v_res_347_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_344_, v_a_boxed_346_);
    return v_res_347_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(
    mut v_toFunctor_348_: *mut leanh::LeanObject,
    mut v_inst_349_: *mut leanh::LeanObject,
    mut v___f_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v___f_352_: *mut leanh::LeanObject,
    mut v_toBind_353_: *mut leanh::LeanObject,
    mut v_a_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_355_ = leanh::lean_ctor_get(v_toFunctor_348_, 0);
    leanh::lean_inc(v_map_355_);
    leanh::lean_dec_ref(v_toFunctor_348_);
    v___x_356_ = leanh::lean_alloc_closure(
        l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_356_, 0, v_a_354_);
    v___x_357_ = leanh::lean_apply_2(v_inst_349_, leanh::lean_box(0), v___x_356_);
    v___x_358_ = leanh::lean_apply_4(
        v_map_355_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_350_,
        v___x_357_,
    );
    v___x_359_ =
        leanh::lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    leanh::lean_closure_set(v___x_359_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_359_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_359_, 2, v_inst_351_);
    leanh::lean_closure_set(v___x_359_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_359_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_359_, 5, v___f_352_);
    v___x_360_ = leanh::lean_apply_4(
        v_toBind_353_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_358_,
        v___x_359_,
    );
    return v___x_360_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg(
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_inst_363_: *mut leanh::LeanObject,
    mut v_a_364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_365_ = leanh::lean_ctor_get(v_inst_362_, 0);
    v_toBind_366_ = leanh::lean_ctor_get(v_inst_362_, 1);
    leanh::lean_inc_n(v_toBind_366_, 2);
    v_toFunctor_367_ = leanh::lean_ctor_get(v_toApplicative_365_, 0);
    v_toPure_368_ = leanh::lean_ctor_get(v_toApplicative_365_, 1);
    v___f_369_ = l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0;
    leanh::lean_inc_n(v_toPure_368_, 2);
    v___f_370_ = leanh::lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_370_, 0, v_toPure_368_);
    leanh::lean_inc_ref(v_inst_362_);
    leanh::lean_inc_ref(v_toFunctor_367_);
    v___f_371_ = leanh::lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_371_, 0, v_toFunctor_367_);
    leanh::lean_closure_set(v___f_371_, 1, v_inst_363_);
    leanh::lean_closure_set(v___f_371_, 2, v___f_369_);
    leanh::lean_closure_set(v___f_371_, 3, v_inst_362_);
    leanh::lean_closure_set(v___f_371_, 4, v___f_370_);
    leanh::lean_closure_set(v___f_371_, 5, v_toBind_366_);
    leanh::lean_inc_ref(v_a_364_);
    v___x_372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_372_, 0, v_a_364_);
    v___x_373_ = leanh::lean_apply_2(v_toPure_368_, leanh::lean_box(0), v___x_372_);
    v___x_374_ =
        leanh::lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    leanh::lean_closure_set(v___x_374_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 2, v_inst_362_);
    leanh::lean_closure_set(v___x_374_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_374_, 5, v___f_371_);
    v___x_375_ = leanh::lean_apply_4(
        v_toBind_366_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_373_,
        v___x_374_,
    );
    return v___x_375_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___boxed(
    mut v_inst_376_: *mut leanh::LeanObject,
    mut v_inst_377_: *mut leanh::LeanObject,
    mut v_a_378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_379_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_376_, v_inst_377_, v_a_378_);
    leanh::lean_dec_ref(v_a_378_);
    return v_res_379_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled(
    mut v_m_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_a_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_384_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_381_, v_inst_382_, v_a_383_);
    return v___x_384_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___boxed(
    mut v_m_385_: *mut leanh::LeanObject,
    mut v_inst_386_: *mut leanh::LeanObject,
    mut v_inst_387_: *mut leanh::LeanObject,
    mut v_a_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_389_ =
        l_Lean_Server_CancellableT_checkCancelled(v_m_385_, v_inst_386_, v_inst_387_, v_a_388_);
    leanh::lean_dec_ref(v_a_388_);
    return v_res_389_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(
    mut v_a_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_392_: u8 = 0;
    v___x_392_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_390_);
    if v___x_392_ == 0 {
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_393_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
        v___x_394_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_394_, 0, v___x_393_);
        return v___x_394_;
    } else {
        let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_395_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
        v___x_396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_396_, 0, v___x_395_);
        return v___x_396_;
    }
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0___boxed(
    mut v_a_397_: *mut leanh::LeanObject,
    mut v___y_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_397_);
    leanh::lean_dec_ref(v_a_397_);
    return v_res_399_;
}
pub unsafe fn l_Lean_Server_CancellableM_checkCancelled(
    mut v_a_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_400_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Server_CancellableM_checkCancelled___boxed(
    mut v_a_403_: *mut leanh::LeanObject,
    mut v_a_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_405_ = l_Lean_Server_CancellableM_checkCancelled(v_a_403_);
    leanh::lean_dec_ref(v_a_403_);
    return v_res_405_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableOfMonadLift___redArg(
    mut v_inst_406_: *mut leanh::LeanObject,
    mut v_inst_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_408_ = leanh::lean_apply_2(v_inst_406_, leanh::lean_box(0), v_inst_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableOfMonadLift(
    mut v_m_409_: *mut leanh::LeanObject,
    mut v_n_410_: *mut leanh::LeanObject,
    mut v_inst_411_: *mut leanh::LeanObject,
    mut v_inst_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = leanh::lean_apply_2(v_inst_411_, leanh::lean_box(0), v_inst_412_);
    return v___x_413_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(
    mut v_inst_414_: *mut leanh::LeanObject,
    mut v_inst_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = leanh::lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_416_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_416_, 1, v_inst_414_);
    leanh::lean_closure_set(v___x_416_, 2, v_inst_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(
    mut v_m_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_420_ = leanh::lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_420_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_420_, 1, v_inst_418_);
    leanh::lean_closure_set(v___x_420_, 2, v_inst_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___redArg(
    mut v_inst_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_421_);
    return v_inst_421_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___redArg___boxed(
    mut v_inst_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_Server_RequestCancellation_check___redArg(v_inst_422_);
    leanh::lean_dec(v_inst_422_);
    return v_res_423_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check(
    mut v_m_424_: *mut leanh::LeanObject,
    mut v_inst_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_425_);
    return v_inst_425_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___boxed(
    mut v_m_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Lean_Server_RequestCancellation_check(v_m_426_, v_inst_427_);
    leanh::lean_dec(v_inst_427_);
    return v_res_428_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_RequestCancellation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_CancelToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Server_RequestCancellation_requestCancelled =
        _init_l_Lean_Server_RequestCancellation_requestCancelled();
    leanh::lean_mark_persistent(l_Lean_Server_RequestCancellation_requestCancelled);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_RequestCancellation(
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
pub unsafe fn initialize_Lean_Server_RequestCancellation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Promise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_CancelToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_RequestCancellation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_RequestCancellation(builtin);
}