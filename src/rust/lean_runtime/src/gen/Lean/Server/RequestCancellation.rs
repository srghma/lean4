// Lean compiler output
// Module: Lean.Server.RequestCancellation
// Imports: Lean.Server.ServerTask Init.System.Promise Init.System.CancelToken
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
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Server_RequestCancellation_requestCancelled: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Server_RequestCancellationToken_new() -> *mut LeanObject {
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_216_ = l_IO_CancelToken_new();
    v___x_217_ = l_IO_CancelToken_new();
    v___x_218_ = lean_io_promise_new();
    v___x_219_ = lean_io_promise_new();
    v___x_220_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_220_, 0, v___x_216_);
    lean_ctor_set(v___x_220_, 1, v___x_217_);
    lean_ctor_set(v___x_220_, 2, v___x_218_);
    lean_ctor_set(v___x_220_, 3, v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_new___boxed(
    mut v_a_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Lean_Server_RequestCancellationToken_new();
    return v_res_222_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(
    mut v_tk_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancelledByCancelRequest_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_requestCancellationPromise_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    v_cancelledByCancelRequest_225_ = lean_ctor_get(v_tk_223_, 0);
    v_requestCancellationPromise_226_ = lean_ctor_get(v_tk_223_, 2);
    v___x_227_ = l_IO_CancelToken_set(v_cancelledByCancelRequest_225_);
    v___x_228_ = lean_box(0);
    v___x_229_ = lean_io_promise_resolve(v___x_228_, v_requestCancellationPromise_226_);
    return v___x_229_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByCancelRequest___boxed(
    mut v_tk_230_: *mut LeanObject,
    mut v_a_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_232_: *mut LeanObject = core::ptr::null_mut();
    v_res_232_ = l_Lean_Server_RequestCancellationToken_cancelByCancelRequest(v_tk_230_);
    lean_dec_ref(v_tk_230_);
    return v_res_232_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByEdit(
    mut v_tk_233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cancelledByEdit_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_editCancellationPromise_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    v_cancelledByEdit_235_ = lean_ctor_get(v_tk_233_, 1);
    v_editCancellationPromise_236_ = lean_ctor_get(v_tk_233_, 3);
    v___x_237_ = l_IO_CancelToken_set(v_cancelledByEdit_235_);
    v___x_238_ = lean_box(0);
    v___x_239_ = lean_io_promise_resolve(v___x_238_, v_editCancellationPromise_236_);
    return v___x_239_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancelByEdit___boxed(
    mut v_tk_240_: *mut LeanObject,
    mut v_a_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lean_Server_RequestCancellationToken_cancelByEdit(v_tk_240_);
    lean_dec_ref(v_tk_240_);
    return v_res_242_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(
    mut v_x_243_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_243_) == 0 {
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        v___x_244_ = lean_box(0);
        return v___x_244_;
    } else {
        let mut v_val_245_: *mut LeanObject = core::ptr::null_mut();
        v_val_245_ = lean_ctor_get(v_x_243_, 0);
        lean_inc(v_val_245_);
        return v_val_245_;
    }
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0___boxed(
    mut v_x_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___lam__0(v_x_246_);
    lean_dec(v_x_246_);
    return v_res_247_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask(
    mut v_tk_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_requestCancellationPromise_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: u8 = 0;
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v_requestCancellationPromise_250_ = lean_ctor_get(v_tk_249_, 2);
    v___f_251_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0;
    v___x_252_ = lean_io_promise_result_opt(v_requestCancellationPromise_250_);
    v___x_253_ = lean_unsigned_to_nat(0);
    v___x_254_ = 1;
    v___x_255_ = lean_task_map(v___f_251_, v___x_252_, v___x_253_, v___x_254_);
    return v___x_255_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_requestCancellationTask___boxed(
    mut v_tk_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_257_: *mut LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_256_);
    lean_dec_ref(v_tk_256_);
    return v_res_257_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_editCancellationTask(
    mut v_tk_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_editCancellationPromise_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_263_: u8 = 0;
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v_editCancellationPromise_259_ = lean_ctor_get(v_tk_258_, 3);
    v___f_260_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask___closed__0;
    v___x_261_ = lean_io_promise_result_opt(v_editCancellationPromise_259_);
    v___x_262_ = lean_unsigned_to_nat(0);
    v___x_263_ = 1;
    v___x_264_ = lean_task_map(v___f_260_, v___x_261_, v___x_262_, v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_editCancellationTask___boxed(
    mut v_tk_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_265_);
    lean_dec_ref(v_tk_265_);
    return v_res_266_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancellationTasks(
    mut v_tk_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_tk_267_);
    v___x_269_ = l_Lean_Server_RequestCancellationToken_editCancellationTask(v_tk_267_);
    v___x_270_ = lean_box(0);
    v___x_271_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_271_, 0, v___x_269_);
    lean_ctor_set(v___x_271_, 1, v___x_270_);
    v___x_272_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_272_, 0, v___x_268_);
    lean_ctor_set(v___x_272_, 1, v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_cancellationTasks___boxed(
    mut v_tk_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_274_: *mut LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_tk_273_);
    lean_dec_ref(v_tk_273_);
    return v_res_274_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(
    mut v_tk_275_: *mut LeanObject,
) -> u8 {
    let mut v_cancelledByCancelRequest_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: u8 = 0;
    v_cancelledByCancelRequest_277_ = lean_ctor_get(v_tk_275_, 0);
    v___x_278_ = l_IO_CancelToken_isSet(v_cancelledByCancelRequest_277_);
    return v___x_278_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed(
    mut v_tk_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_281_: u8 = 0;
    let mut v_r_282_: *mut LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_tk_279_);
    lean_dec_ref(v_tk_279_);
    v_r_282_ = lean_box((v_res_281_) as usize);
    return v_r_282_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(
    mut v_tk_283_: *mut LeanObject,
) -> u8 {
    let mut v_cancelledByEdit_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    v_cancelledByEdit_285_ = lean_ctor_get(v_tk_283_, 1);
    v___x_286_ = l_IO_CancelToken_isSet(v_cancelledByEdit_285_);
    return v___x_286_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelledByEdit___boxed(
    mut v_tk_287_: *mut LeanObject,
    mut v_a_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: u8 = 0;
    let mut v_r_290_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Lean_Server_RequestCancellationToken_wasCancelledByEdit(v_tk_287_);
    lean_dec_ref(v_tk_287_);
    v_r_290_ = lean_box((v_res_289_) as usize);
    return v_r_290_;
}
pub unsafe fn l_Lean_Server_RequestCancellationToken_wasCancelled(
    mut v_tk_291_: *mut LeanObject,
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
    mut v_tk_295_: *mut LeanObject,
    mut v_a_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_297_: u8 = 0;
    let mut v_r_298_: *mut LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_tk_295_);
    lean_dec_ref(v_tk_295_);
    v_r_298_ = lean_box((v_res_297_) as usize);
    return v_r_298_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_toCtorIdx(
    mut v_x_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = lean_unsigned_to_nat(0);
    return v___x_300_;
}
pub unsafe fn _init_l_Lean_Server_RequestCancellation_requestCancelled() -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_box(0);
    return v___x_301_;
}
pub unsafe fn l_Lean_Server_CancellableT_run___redArg(
    mut v_tk_302_: *mut LeanObject,
    mut v_x_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = lean_apply_1(v_x_303_, v_tk_302_);
    return v___x_304_;
}
pub unsafe fn l_Lean_Server_CancellableT_run(
    mut v_m_305_: *mut LeanObject,
    mut v_00_u03b1_306_: *mut LeanObject,
    mut v_tk_307_: *mut LeanObject,
    mut v_x_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    v___x_309_ = lean_apply_1(v_x_308_, v_tk_307_);
    return v___x_309_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___redArg(
    mut v_tk_310_: *mut LeanObject,
    mut v_x_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    v___x_313_ = lean_apply_2(v_x_311_, v_tk_310_, lean_box(0));
    return v___x_313_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___redArg___boxed(
    mut v_tk_314_: *mut LeanObject,
    mut v_x_315_: *mut LeanObject,
    mut v_a_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_317_: *mut LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Lean_Server_CancellableM_run___redArg(v_tk_314_, v_x_315_);
    return v_res_317_;
}
pub unsafe fn l_Lean_Server_CancellableM_run(
    mut v_00_u03b1_318_: *mut LeanObject,
    mut v_tk_319_: *mut LeanObject,
    mut v_x_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_apply_2(v_x_320_, v_tk_319_, lean_box(0));
    return v___x_322_;
}
pub unsafe fn l_Lean_Server_CancellableM_run___boxed(
    mut v_00_u03b1_323_: *mut LeanObject,
    mut v_tk_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Lean_Server_CancellableM_run(v_00_u03b1_323_, v_tk_324_, v_x_325_);
    return v_res_327_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(
    mut v_a_328_: u8,
) -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___x_329_ = lean_box((v_a_328_) as usize);
    v___x_330_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_330_, 0, v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0___boxed(
    mut v_a_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_668__boxed_332_: u8 = 0;
    let mut v_res_333_: *mut LeanObject = core::ptr::null_mut();
    v_a_668__boxed_332_ = (lean_unbox(v_a_331_) as u8);
    v_res_333_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__0(v_a_668__boxed_332_);
    return v_res_333_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(
    mut v_toPure_338_: *mut LeanObject,
    mut v_a_339_: u8,
) -> *mut LeanObject {
    if v_a_339_ == 0 {
        let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
        v___x_340_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
        v___x_341_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_340_);
        return v___x_341_;
    } else {
        let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
        v___x_342_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
        v___x_343_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_342_);
        return v___x_343_;
    }
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed(
    mut v_toPure_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_346_: u8 = 0;
    let mut v_res_347_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_346_ = (lean_unbox(v_a_345_) as u8);
    v_res_347_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1(v_toPure_344_, v_a_boxed_346_);
    return v_res_347_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2(
    mut v_toFunctor_348_: *mut LeanObject,
    mut v_inst_349_: *mut LeanObject,
    mut v___f_350_: *mut LeanObject,
    mut v_inst_351_: *mut LeanObject,
    mut v___f_352_: *mut LeanObject,
    mut v_toBind_353_: *mut LeanObject,
    mut v_a_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    v_map_355_ = lean_ctor_get(v_toFunctor_348_, 0);
    lean_inc(v_map_355_);
    lean_dec_ref(v_toFunctor_348_);
    v___x_356_ = lean_alloc_closure(
        l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___x_356_, 0, v_a_354_);
    v___x_357_ = lean_apply_2(v_inst_349_, lean_box(0), v___x_356_);
    v___x_358_ = lean_apply_4(v_map_355_, lean_box(0), lean_box(0), v___f_350_, v___x_357_);
    v___x_359_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_359_, 0, lean_box(0));
    lean_closure_set(v___x_359_, 1, lean_box(0));
    lean_closure_set(v___x_359_, 2, v_inst_351_);
    lean_closure_set(v___x_359_, 3, lean_box(0));
    lean_closure_set(v___x_359_, 4, lean_box(0));
    lean_closure_set(v___x_359_, 5, v___f_352_);
    v___x_360_ = lean_apply_4(
        v_toBind_353_,
        lean_box(0),
        lean_box(0),
        v___x_358_,
        v___x_359_,
    );
    return v___x_360_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg(
    mut v_inst_362_: *mut LeanObject,
    mut v_inst_363_: *mut LeanObject,
    mut v_a_364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_365_ = lean_ctor_get(v_inst_362_, 0);
    v_toBind_366_ = lean_ctor_get(v_inst_362_, 1);
    lean_inc_n(v_toBind_366_, 2);
    v_toFunctor_367_ = lean_ctor_get(v_toApplicative_365_, 0);
    v_toPure_368_ = lean_ctor_get(v_toApplicative_365_, 1);
    v___f_369_ = l_Lean_Server_CancellableT_checkCancelled___redArg___closed__0;
    lean_inc_n(v_toPure_368_, 2);
    v___f_370_ = lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_370_, 0, v_toPure_368_);
    lean_inc_ref(v_inst_362_);
    lean_inc_ref(v_toFunctor_367_);
    v___f_371_ = lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_371_, 0, v_toFunctor_367_);
    lean_closure_set(v___f_371_, 1, v_inst_363_);
    lean_closure_set(v___f_371_, 2, v___f_369_);
    lean_closure_set(v___f_371_, 3, v_inst_362_);
    lean_closure_set(v___f_371_, 4, v___f_370_);
    lean_closure_set(v___f_371_, 5, v_toBind_366_);
    lean_inc_ref(v_a_364_);
    v___x_372_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_372_, 0, v_a_364_);
    v___x_373_ = lean_apply_2(v_toPure_368_, lean_box(0), v___x_372_);
    v___x_374_ = lean_alloc_closure(l_ExceptT_bindCont as *mut core::ffi::c_void, 7, 6);
    lean_closure_set(v___x_374_, 0, lean_box(0));
    lean_closure_set(v___x_374_, 1, lean_box(0));
    lean_closure_set(v___x_374_, 2, v_inst_362_);
    lean_closure_set(v___x_374_, 3, lean_box(0));
    lean_closure_set(v___x_374_, 4, lean_box(0));
    lean_closure_set(v___x_374_, 5, v___f_371_);
    v___x_375_ = lean_apply_4(
        v_toBind_366_,
        lean_box(0),
        lean_box(0),
        v___x_373_,
        v___x_374_,
    );
    return v___x_375_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___redArg___boxed(
    mut v_inst_376_: *mut LeanObject,
    mut v_inst_377_: *mut LeanObject,
    mut v_a_378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_379_: *mut LeanObject = core::ptr::null_mut();
    v_res_379_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_376_, v_inst_377_, v_a_378_);
    lean_dec_ref(v_a_378_);
    return v_res_379_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled(
    mut v_m_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_a_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ =
        l_Lean_Server_CancellableT_checkCancelled___redArg(v_inst_381_, v_inst_382_, v_a_383_);
    return v___x_384_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___boxed(
    mut v_m_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_inst_387_: *mut LeanObject,
    mut v_a_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_389_: *mut LeanObject = core::ptr::null_mut();
    v_res_389_ =
        l_Lean_Server_CancellableT_checkCancelled(v_m_385_, v_inst_386_, v_inst_387_, v_a_388_);
    lean_dec_ref(v_a_388_);
    return v_res_389_;
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(
    mut v_a_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: u8 = 0;
    v___x_392_ = l_Lean_Server_RequestCancellationToken_wasCancelledByCancelRequest(v_a_390_);
    if v___x_392_ == 0 {
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
        v___x_393_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__0;
        v___x_394_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_394_, 0, v___x_393_);
        return v___x_394_;
    } else {
        let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        v___x_395_ = l_Lean_Server_CancellableT_checkCancelled___redArg___lam__1___closed__1;
        v___x_396_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_396_, 0, v___x_395_);
        return v___x_396_;
    }
}
pub unsafe fn l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0___boxed(
    mut v_a_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_399_: *mut LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_397_);
    lean_dec_ref(v_a_397_);
    return v_res_399_;
}
pub unsafe fn l_Lean_Server_CancellableM_checkCancelled(
    mut v_a_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    v___x_402_ = l_Lean_Server_CancellableT_checkCancelled___at___00Lean_Server_CancellableM_checkCancelled_spec__0(v_a_400_);
    return v___x_402_;
}
pub unsafe fn l_Lean_Server_CancellableM_checkCancelled___boxed(
    mut v_a_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_405_: *mut LeanObject = core::ptr::null_mut();
    v_res_405_ = l_Lean_Server_CancellableM_checkCancelled(v_a_403_);
    lean_dec_ref(v_a_403_);
    return v_res_405_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableOfMonadLift___redArg(
    mut v_inst_406_: *mut LeanObject,
    mut v_inst_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_408_ = lean_apply_2(v_inst_406_, lean_box(0), v_inst_407_);
    return v___x_408_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableOfMonadLift(
    mut v_m_409_: *mut LeanObject,
    mut v_n_410_: *mut LeanObject,
    mut v_inst_411_: *mut LeanObject,
    mut v_inst_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = lean_apply_2(v_inst_411_, lean_box(0), v_inst_412_);
    return v___x_413_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO___redArg(
    mut v_inst_414_: *mut LeanObject,
    mut v_inst_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_416_ = lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_416_, 0, lean_box(0));
    lean_closure_set(v___x_416_, 1, v_inst_414_);
    lean_closure_set(v___x_416_, 2, v_inst_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_Server_instMonadCancellableCancellableTOfMonadOfMonadLiftTBaseIO(
    mut v_m_417_: *mut LeanObject,
    mut v_inst_418_: *mut LeanObject,
    mut v_inst_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    v___x_420_ = lean_alloc_closure(
        l_Lean_Server_CancellableT_checkCancelled___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_420_, 0, lean_box(0));
    lean_closure_set(v___x_420_, 1, v_inst_418_);
    lean_closure_set(v___x_420_, 2, v_inst_419_);
    return v___x_420_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___redArg(
    mut v_inst_421_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_421_);
    return v_inst_421_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___redArg___boxed(
    mut v_inst_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_423_: *mut LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_Server_RequestCancellation_check___redArg(v_inst_422_);
    lean_dec(v_inst_422_);
    return v_res_423_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check(
    mut v_m_424_: *mut LeanObject,
    mut v_inst_425_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_425_);
    return v_inst_425_;
}
pub unsafe fn l_Lean_Server_RequestCancellation_check___boxed(
    mut v_m_426_: *mut LeanObject,
    mut v_inst_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_428_: *mut LeanObject = core::ptr::null_mut();
    v_res_428_ = l_Lean_Server_RequestCancellation_check(v_m_426_, v_inst_427_);
    lean_dec(v_inst_427_);
    return v_res_428_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_RequestCancellation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_CancelToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Server_RequestCancellation_requestCancelled =
        _init_l_Lean_Server_RequestCancellation_requestCancelled();
    lean_mark_persistent(l_Lean_Server_RequestCancellation_requestCancelled);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_RequestCancellation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_RequestCancellation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_ServerTask(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_CancelToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_RequestCancellation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_RequestCancellation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_RequestCancellation(builtin);
}
