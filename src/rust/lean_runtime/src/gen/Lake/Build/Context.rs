// Lean compiler output
// Module: Lake.Build.Context
// Imports: Lake.Config.Cache Lake.Config.Context Lake.Build.Job.Basic
use crate::r#gen::Lake::Build::Job::Basic::{
    initialize_Lake_Build_Job_Basic, runtime_initialize_Lake_Build_Job_Basic,
};
use crate::r#gen::Lake::Config::Cache::{
    initialize_Lake_Config_Cache, runtime_initialize_Lake_Config_Cache,
};
use crate::r#gen::Lake::Config::Context::{
    initialize_Lake_Config_Context, runtime_initialize_Lake_Config_Context,
};
use crate::r#gen::Lake::Util::Log::l_Lake_instDecidableEqVerbosity;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::lean_st_mk_ref;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub static l_Lake_mkJobQueue___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_mkJobQueue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_mkJobQueue___closed__0_value) as *mut LeanObject;
pub static l_Lake_getLeanTrace___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanTrace___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanTrace___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanTrace___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getBuildConfig___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getBuildConfig___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getBuildConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getBuildConfig___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getIsOldMode___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getIsOldMode___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getIsOldMode___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getIsOldMode___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getTrustHash___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getTrustHash___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getTrustHash___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getTrustHash___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getNoBuild___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_getNoBuild___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getNoBuild___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getNoBuild___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getVerbosity___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getVerbosity___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getVerbosity___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getVerbosity___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getIsVerbose___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getIsVerbose___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getIsVerbose___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getIsVerbose___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getIsQuiet___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_getIsQuiet___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_getIsQuiet___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getIsQuiet___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_getLeanOptOverrides___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_getLeanOptOverrides___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_getLeanOptOverrides___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_getLeanOptOverrides___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_BuildConfig_showProgress(mut v_cfg_231_: *mut LeanObject) -> u8 {
    let mut v_noBuild_232_: u8 = 0;
    let mut v_verbosity_233_: u8 = 0;
    let mut v___x_235_: u8 = 0;
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: u8 = 0;
    let mut v___x_238_: u8 = 0;
    let mut v___x_239_: u8 = 0;
    let mut v___x_240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_noBuild_232_ = lean_ctor_get_uint8(
                    v_cfg_231_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                );
                v_verbosity_233_ = lean_ctor_get_uint8(
                    v_cfg_231_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                );
                if v_noBuild_232_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_239_ = 2;
                    v___x_240_ = l_Lake_instDecidableEqVerbosity(v_verbosity_233_, v___x_239_);
                    if v___x_240_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v___x_240_;
                    }
                }
            }
            1 => {
                v___x_235_ = 0;
                v___x_236_ = l_Lake_instDecidableEqVerbosity(v_verbosity_233_, v___x_235_);
                if v___x_236_ == 0 {
                    v___x_237_ = 1;
                    return v___x_237_;
                } else {
                    v___x_238_ = 0;
                    return v___x_238_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildConfig_showProgress___boxed(
    mut v_cfg_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_242_: u8 = 0;
    let mut v_r_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_242_ = l_Lake_BuildConfig_showProgress(v_cfg_241_);
    lean_dec_ref(v_cfg_241_);
    v_r_243_ = lean_box((v_res_242_) as usize);
    return v_r_243_;
}
pub unsafe fn l_Lake_mkJobQueue() -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = l_Lake_mkJobQueue___closed__0;
    v___x_248_ = lean_st_mk_ref(v___x_247_);
    return v___x_248_;
}
pub unsafe fn l_Lake_mkJobQueue___boxed(mut v_a_249_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_250_: *mut LeanObject = core::ptr::null_mut();
    v_res_250_ = l_Lake_mkJobQueue();
    return v_res_250_;
}
pub unsafe fn l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0(
    mut v_inst_251_: *mut LeanObject,
    mut v_00_u03b1_252_: *mut LeanObject,
    mut v_x_253_: *mut LeanObject,
    mut v_ctx_254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toContext_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    v_toContext_255_ = lean_ctor_get(v_ctx_254_, 1);
    lean_inc(v_toContext_255_);
    lean_dec_ref(v_ctx_254_);
    v___x_256_ = lean_apply_1(v_x_253_, v_toContext_255_);
    v___x_257_ = lean_apply_2(v_inst_251_, lean_box(0), v___x_256_);
    return v___x_257_;
}
pub unsafe fn l_Lake_instMonadLiftLakeMBuildTOfPure___redArg(
    mut v_inst_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_259_: *mut LeanObject = core::ptr::null_mut();
    v___f_259_ = lean_alloc_closure(
        l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_259_, 0, v_inst_258_);
    return v___f_259_;
}
pub unsafe fn l_Lake_instMonadLiftLakeMBuildTOfPure(
    mut v_m_260_: *mut LeanObject,
    mut v_inst_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_262_: *mut LeanObject = core::ptr::null_mut();
    v___f_262_ = lean_alloc_closure(
        l_Lake_instMonadLiftLakeMBuildTOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_262_, 0, v_inst_261_);
    return v___f_262_;
}
pub unsafe fn l_Lake_getBuildContext___redArg(mut v_inst_263_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_263_);
    return v_inst_263_;
}
pub unsafe fn l_Lake_getBuildContext___redArg___boxed(
    mut v_inst_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_265_: *mut LeanObject = core::ptr::null_mut();
    v_res_265_ = l_Lake_getBuildContext___redArg(v_inst_264_);
    lean_dec(v_inst_264_);
    return v_res_265_;
}
pub unsafe fn l_Lake_getBuildContext(
    mut v_m_266_: *mut LeanObject,
    mut v_inst_267_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_267_);
    return v_inst_267_;
}
pub unsafe fn l_Lake_getBuildContext___boxed(
    mut v_m_268_: *mut LeanObject,
    mut v_inst_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_270_: *mut LeanObject = core::ptr::null_mut();
    v_res_270_ = l_Lake_getBuildContext(v_m_268_, v_inst_269_);
    lean_dec(v_inst_269_);
    return v_res_270_;
}
pub unsafe fn l_Lake_getLeanTrace___redArg___lam__0(
    mut v_x_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_leanTrace_272_: *mut LeanObject = core::ptr::null_mut();
    v_leanTrace_272_ = lean_ctor_get(v_x_271_, 2);
    lean_inc_ref(v_leanTrace_272_);
    return v_leanTrace_272_;
}
pub unsafe fn l_Lake_getLeanTrace___redArg___lam__0___boxed(
    mut v_x_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_274_: *mut LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lake_getLeanTrace___redArg___lam__0(v_x_273_);
    lean_dec_ref(v_x_273_);
    return v_res_274_;
}
pub unsafe fn l_Lake_getLeanTrace___redArg(
    mut v_inst_276_: *mut LeanObject,
    mut v_inst_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    v_map_278_ = lean_ctor_get(v_inst_276_, 0);
    lean_inc(v_map_278_);
    lean_dec_ref(v_inst_276_);
    v___f_279_ = l_Lake_getLeanTrace___redArg___closed__0;
    v___x_280_ = lean_apply_4(
        v_map_278_,
        lean_box(0),
        lean_box(0),
        v___f_279_,
        v_inst_277_,
    );
    return v___x_280_;
}
pub unsafe fn l_Lake_getLeanTrace(
    mut v_m_281_: *mut LeanObject,
    mut v_inst_282_: *mut LeanObject,
    mut v_inst_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v_map_284_ = lean_ctor_get(v_inst_282_, 0);
    lean_inc(v_map_284_);
    lean_dec_ref(v_inst_282_);
    v___f_285_ = l_Lake_getLeanTrace___redArg___closed__0;
    v___x_286_ = lean_apply_4(
        v_map_284_,
        lean_box(0),
        lean_box(0),
        v___f_285_,
        v_inst_283_,
    );
    return v___x_286_;
}
pub unsafe fn l_Lake_getBuildConfig___redArg___lam__0(
    mut v_x_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBuildConfig_288_: *mut LeanObject = core::ptr::null_mut();
    v_toBuildConfig_288_ = lean_ctor_get(v_x_287_, 0);
    lean_inc_ref(v_toBuildConfig_288_);
    return v_toBuildConfig_288_;
}
pub unsafe fn l_Lake_getBuildConfig___redArg___lam__0___boxed(
    mut v_x_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_290_: *mut LeanObject = core::ptr::null_mut();
    v_res_290_ = l_Lake_getBuildConfig___redArg___lam__0(v_x_289_);
    lean_dec_ref(v_x_289_);
    return v_res_290_;
}
pub unsafe fn l_Lake_getBuildConfig___redArg(
    mut v_inst_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    v_map_294_ = lean_ctor_get(v_inst_292_, 0);
    lean_inc(v_map_294_);
    lean_dec_ref(v_inst_292_);
    v___f_295_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_296_ = lean_apply_4(
        v_map_294_,
        lean_box(0),
        lean_box(0),
        v___f_295_,
        v_inst_293_,
    );
    return v___x_296_;
}
pub unsafe fn l_Lake_getBuildConfig(
    mut v_m_297_: *mut LeanObject,
    mut v_inst_298_: *mut LeanObject,
    mut v_inst_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v_map_300_ = lean_ctor_get(v_inst_298_, 0);
    lean_inc(v_map_300_);
    lean_dec_ref(v_inst_298_);
    v___f_301_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_302_ = lean_apply_4(
        v_map_300_,
        lean_box(0),
        lean_box(0),
        v___f_301_,
        v_inst_299_,
    );
    return v___x_302_;
}
pub unsafe fn l_Lake_getIsOldMode___redArg___lam__0(mut v_x_303_: *mut LeanObject) -> u8 {
    let mut v_oldMode_304_: u8 = 0;
    v_oldMode_304_ = lean_ctor_get_uint8(
        v_x_303_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    return v_oldMode_304_;
}
pub unsafe fn l_Lake_getIsOldMode___redArg___lam__0___boxed(
    mut v_x_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: u8 = 0;
    let mut v_r_307_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = l_Lake_getIsOldMode___redArg___lam__0(v_x_305_);
    lean_dec_ref(v_x_305_);
    v_r_307_ = lean_box((v_res_306_) as usize);
    return v_r_307_;
}
pub unsafe fn l_Lake_getIsOldMode___redArg(
    mut v_inst_309_: *mut LeanObject,
    mut v_inst_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v_map_311_ = lean_ctor_get(v_inst_309_, 0);
    lean_inc_n(v_map_311_, 2);
    lean_dec_ref(v_inst_309_);
    v___f_312_ = l_Lake_getIsOldMode___redArg___closed__0;
    v___f_313_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_314_ = lean_apply_4(
        v_map_311_,
        lean_box(0),
        lean_box(0),
        v___f_313_,
        v_inst_310_,
    );
    v___x_315_ = lean_apply_4(v_map_311_, lean_box(0), lean_box(0), v___f_312_, v___x_314_);
    return v___x_315_;
}
pub unsafe fn l_Lake_getIsOldMode(
    mut v_m_316_: *mut LeanObject,
    mut v_inst_317_: *mut LeanObject,
    mut v_inst_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v_map_319_ = lean_ctor_get(v_inst_317_, 0);
    lean_inc_n(v_map_319_, 2);
    lean_dec_ref(v_inst_317_);
    v___f_320_ = l_Lake_getIsOldMode___redArg___closed__0;
    v___f_321_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_322_ = lean_apply_4(
        v_map_319_,
        lean_box(0),
        lean_box(0),
        v___f_321_,
        v_inst_318_,
    );
    v___x_323_ = lean_apply_4(v_map_319_, lean_box(0), lean_box(0), v___f_320_, v___x_322_);
    return v___x_323_;
}
pub unsafe fn l_Lake_getTrustHash___redArg___lam__0(mut v_x_324_: *mut LeanObject) -> u8 {
    let mut v_trustHash_325_: u8 = 0;
    v_trustHash_325_ = lean_ctor_get_uint8(
        v_x_324_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
    );
    return v_trustHash_325_;
}
pub unsafe fn l_Lake_getTrustHash___redArg___lam__0___boxed(
    mut v_x_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: u8 = 0;
    let mut v_r_328_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Lake_getTrustHash___redArg___lam__0(v_x_326_);
    lean_dec_ref(v_x_326_);
    v_r_328_ = lean_box((v_res_327_) as usize);
    return v_r_328_;
}
pub unsafe fn l_Lake_getTrustHash___redArg(
    mut v_inst_330_: *mut LeanObject,
    mut v_inst_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v_map_332_ = lean_ctor_get(v_inst_330_, 0);
    lean_inc_n(v_map_332_, 2);
    lean_dec_ref(v_inst_330_);
    v___f_333_ = l_Lake_getTrustHash___redArg___closed__0;
    v___f_334_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_335_ = lean_apply_4(
        v_map_332_,
        lean_box(0),
        lean_box(0),
        v___f_334_,
        v_inst_331_,
    );
    v___x_336_ = lean_apply_4(v_map_332_, lean_box(0), lean_box(0), v___f_333_, v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Lake_getTrustHash(
    mut v_m_337_: *mut LeanObject,
    mut v_inst_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    v_map_340_ = lean_ctor_get(v_inst_338_, 0);
    lean_inc_n(v_map_340_, 2);
    lean_dec_ref(v_inst_338_);
    v___f_341_ = l_Lake_getTrustHash___redArg___closed__0;
    v___f_342_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_343_ = lean_apply_4(
        v_map_340_,
        lean_box(0),
        lean_box(0),
        v___f_342_,
        v_inst_339_,
    );
    v___x_344_ = lean_apply_4(v_map_340_, lean_box(0), lean_box(0), v___f_341_, v___x_343_);
    return v___x_344_;
}
pub unsafe fn l_Lake_getNoBuild___redArg___lam__0(mut v_x_345_: *mut LeanObject) -> u8 {
    let mut v_noBuild_346_: u8 = 0;
    v_noBuild_346_ = lean_ctor_get_uint8(
        v_x_345_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
    );
    return v_noBuild_346_;
}
pub unsafe fn l_Lake_getNoBuild___redArg___lam__0___boxed(
    mut v_x_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_348_: u8 = 0;
    let mut v_r_349_: *mut LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Lake_getNoBuild___redArg___lam__0(v_x_347_);
    lean_dec_ref(v_x_347_);
    v_r_349_ = lean_box((v_res_348_) as usize);
    return v_r_349_;
}
pub unsafe fn l_Lake_getNoBuild___redArg(
    mut v_inst_351_: *mut LeanObject,
    mut v_inst_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    v_map_353_ = lean_ctor_get(v_inst_351_, 0);
    lean_inc_n(v_map_353_, 2);
    lean_dec_ref(v_inst_351_);
    v___f_354_ = l_Lake_getNoBuild___redArg___closed__0;
    v___f_355_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_356_ = lean_apply_4(
        v_map_353_,
        lean_box(0),
        lean_box(0),
        v___f_355_,
        v_inst_352_,
    );
    v___x_357_ = lean_apply_4(v_map_353_, lean_box(0), lean_box(0), v___f_354_, v___x_356_);
    return v___x_357_;
}
pub unsafe fn l_Lake_getNoBuild(
    mut v_m_358_: *mut LeanObject,
    mut v_inst_359_: *mut LeanObject,
    mut v_inst_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v_map_361_ = lean_ctor_get(v_inst_359_, 0);
    lean_inc_n(v_map_361_, 2);
    lean_dec_ref(v_inst_359_);
    v___f_362_ = l_Lake_getNoBuild___redArg___closed__0;
    v___f_363_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_364_ = lean_apply_4(
        v_map_361_,
        lean_box(0),
        lean_box(0),
        v___f_363_,
        v_inst_360_,
    );
    v___x_365_ = lean_apply_4(v_map_361_, lean_box(0), lean_box(0), v___f_362_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Lake_getVerbosity___redArg___lam__0(mut v_x_366_: *mut LeanObject) -> u8 {
    let mut v_verbosity_367_: u8 = 0;
    v_verbosity_367_ = lean_ctor_get_uint8(
        v_x_366_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
    );
    return v_verbosity_367_;
}
pub unsafe fn l_Lake_getVerbosity___redArg___lam__0___boxed(
    mut v_x_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_369_: u8 = 0;
    let mut v_r_370_: *mut LeanObject = core::ptr::null_mut();
    v_res_369_ = l_Lake_getVerbosity___redArg___lam__0(v_x_368_);
    lean_dec_ref(v_x_368_);
    v_r_370_ = lean_box((v_res_369_) as usize);
    return v_r_370_;
}
pub unsafe fn l_Lake_getVerbosity___redArg(
    mut v_inst_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    v_map_374_ = lean_ctor_get(v_inst_372_, 0);
    lean_inc_n(v_map_374_, 2);
    lean_dec_ref(v_inst_372_);
    v___f_375_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_376_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_377_ = lean_apply_4(
        v_map_374_,
        lean_box(0),
        lean_box(0),
        v___f_376_,
        v_inst_373_,
    );
    v___x_378_ = lean_apply_4(v_map_374_, lean_box(0), lean_box(0), v___f_375_, v___x_377_);
    return v___x_378_;
}
pub unsafe fn l_Lake_getVerbosity(
    mut v_m_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v_map_382_ = lean_ctor_get(v_inst_380_, 0);
    lean_inc_n(v_map_382_, 2);
    lean_dec_ref(v_inst_380_);
    v___f_383_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_384_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_385_ = lean_apply_4(
        v_map_382_,
        lean_box(0),
        lean_box(0),
        v___f_384_,
        v_inst_381_,
    );
    v___x_386_ = lean_apply_4(v_map_382_, lean_box(0), lean_box(0), v___f_383_, v___x_385_);
    return v___x_386_;
}
pub unsafe fn l_Lake_getIsVerbose___redArg___lam__0(mut v_x_387_: u8) -> u8 {
    let mut v___x_388_: u8 = 0;
    let mut v___x_389_: u8 = 0;
    v___x_388_ = 2;
    v___x_389_ = l_Lake_instDecidableEqVerbosity(v_x_387_, v___x_388_);
    return v___x_389_;
}
pub unsafe fn l_Lake_getIsVerbose___redArg___lam__0___boxed(
    mut v_x_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_54__boxed_391_: u8 = 0;
    let mut v_res_392_: u8 = 0;
    let mut v_r_393_: *mut LeanObject = core::ptr::null_mut();
    v_x_54__boxed_391_ = (lean_unbox(v_x_390_) as u8);
    v_res_392_ = l_Lake_getIsVerbose___redArg___lam__0(v_x_54__boxed_391_);
    v_r_393_ = lean_box((v_res_392_) as usize);
    return v_r_393_;
}
pub unsafe fn l_Lake_getIsVerbose___redArg(
    mut v_inst_395_: *mut LeanObject,
    mut v_inst_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    v_map_397_ = lean_ctor_get(v_inst_395_, 0);
    lean_inc_n(v_map_397_, 3);
    lean_dec_ref(v_inst_395_);
    v___f_398_ = l_Lake_getIsVerbose___redArg___closed__0;
    v___f_399_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_400_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_401_ = lean_apply_4(
        v_map_397_,
        lean_box(0),
        lean_box(0),
        v___f_400_,
        v_inst_396_,
    );
    v___x_402_ = lean_apply_4(v_map_397_, lean_box(0), lean_box(0), v___f_399_, v___x_401_);
    v___x_403_ = lean_apply_4(v_map_397_, lean_box(0), lean_box(0), v___f_398_, v___x_402_);
    return v___x_403_;
}
pub unsafe fn l_Lake_getIsVerbose(
    mut v_m_404_: *mut LeanObject,
    mut v_inst_405_: *mut LeanObject,
    mut v_inst_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    v_map_407_ = lean_ctor_get(v_inst_405_, 0);
    lean_inc_n(v_map_407_, 3);
    lean_dec_ref(v_inst_405_);
    v___f_408_ = l_Lake_getIsVerbose___redArg___closed__0;
    v___f_409_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_410_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_411_ = lean_apply_4(
        v_map_407_,
        lean_box(0),
        lean_box(0),
        v___f_410_,
        v_inst_406_,
    );
    v___x_412_ = lean_apply_4(v_map_407_, lean_box(0), lean_box(0), v___f_409_, v___x_411_);
    v___x_413_ = lean_apply_4(v_map_407_, lean_box(0), lean_box(0), v___f_408_, v___x_412_);
    return v___x_413_;
}
pub unsafe fn l_Lake_getIsQuiet___redArg___lam__0(mut v_x_414_: u8) -> u8 {
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: u8 = 0;
    v___x_415_ = 0;
    v___x_416_ = l_Lake_instDecidableEqVerbosity(v_x_414_, v___x_415_);
    return v___x_416_;
}
pub unsafe fn l_Lake_getIsQuiet___redArg___lam__0___boxed(
    mut v_x_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_54__boxed_418_: u8 = 0;
    let mut v_res_419_: u8 = 0;
    let mut v_r_420_: *mut LeanObject = core::ptr::null_mut();
    v_x_54__boxed_418_ = (lean_unbox(v_x_417_) as u8);
    v_res_419_ = l_Lake_getIsQuiet___redArg___lam__0(v_x_54__boxed_418_);
    v_r_420_ = lean_box((v_res_419_) as usize);
    return v_r_420_;
}
pub unsafe fn l_Lake_getIsQuiet___redArg(
    mut v_inst_422_: *mut LeanObject,
    mut v_inst_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v_map_424_ = lean_ctor_get(v_inst_422_, 0);
    lean_inc_n(v_map_424_, 3);
    lean_dec_ref(v_inst_422_);
    v___f_425_ = l_Lake_getIsQuiet___redArg___closed__0;
    v___f_426_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_427_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_428_ = lean_apply_4(
        v_map_424_,
        lean_box(0),
        lean_box(0),
        v___f_427_,
        v_inst_423_,
    );
    v___x_429_ = lean_apply_4(v_map_424_, lean_box(0), lean_box(0), v___f_426_, v___x_428_);
    v___x_430_ = lean_apply_4(v_map_424_, lean_box(0), lean_box(0), v___f_425_, v___x_429_);
    return v___x_430_;
}
pub unsafe fn l_Lake_getIsQuiet(
    mut v_m_431_: *mut LeanObject,
    mut v_inst_432_: *mut LeanObject,
    mut v_inst_433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    v_map_434_ = lean_ctor_get(v_inst_432_, 0);
    lean_inc_n(v_map_434_, 3);
    lean_dec_ref(v_inst_432_);
    v___f_435_ = l_Lake_getIsQuiet___redArg___closed__0;
    v___f_436_ = l_Lake_getVerbosity___redArg___closed__0;
    v___f_437_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_438_ = lean_apply_4(
        v_map_434_,
        lean_box(0),
        lean_box(0),
        v___f_437_,
        v_inst_433_,
    );
    v___x_439_ = lean_apply_4(v_map_434_, lean_box(0), lean_box(0), v___f_436_, v___x_438_);
    v___x_440_ = lean_apply_4(v_map_434_, lean_box(0), lean_box(0), v___f_435_, v___x_439_);
    return v___x_440_;
}
pub unsafe fn l_Lake_getLeanOptOverrides___redArg___lam__0(
    mut v_x_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_leanOptOverrides_442_: *mut LeanObject = core::ptr::null_mut();
    v_leanOptOverrides_442_ = lean_ctor_get(v_x_441_, 2);
    lean_inc(v_leanOptOverrides_442_);
    return v_leanOptOverrides_442_;
}
pub unsafe fn l_Lake_getLeanOptOverrides___redArg___lam__0___boxed(
    mut v_x_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_444_: *mut LeanObject = core::ptr::null_mut();
    v_res_444_ = l_Lake_getLeanOptOverrides___redArg___lam__0(v_x_443_);
    lean_dec_ref(v_x_443_);
    return v_res_444_;
}
pub unsafe fn l_Lake_getLeanOptOverrides___redArg(
    mut v_inst_446_: *mut LeanObject,
    mut v_inst_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    v_map_448_ = lean_ctor_get(v_inst_446_, 0);
    lean_inc_n(v_map_448_, 2);
    lean_dec_ref(v_inst_446_);
    v___f_449_ = l_Lake_getLeanOptOverrides___redArg___closed__0;
    v___f_450_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_451_ = lean_apply_4(
        v_map_448_,
        lean_box(0),
        lean_box(0),
        v___f_450_,
        v_inst_447_,
    );
    v___x_452_ = lean_apply_4(v_map_448_, lean_box(0), lean_box(0), v___f_449_, v___x_451_);
    return v___x_452_;
}
pub unsafe fn l_Lake_getLeanOptOverrides(
    mut v_m_453_: *mut LeanObject,
    mut v_inst_454_: *mut LeanObject,
    mut v_inst_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    v_map_456_ = lean_ctor_get(v_inst_454_, 0);
    lean_inc_n(v_map_456_, 2);
    lean_dec_ref(v_inst_454_);
    v___f_457_ = l_Lake_getLeanOptOverrides___redArg___closed__0;
    v___f_458_ = l_Lake_getBuildConfig___redArg___closed__0;
    v___x_459_ = lean_apply_4(
        v_map_456_,
        lean_box(0),
        lean_box(0),
        v___f_458_,
        v_inst_455_,
    );
    v___x_460_ = lean_apply_4(v_map_456_, lean_box(0), lean_box(0), v___f_457_, v___x_459_);
    return v___x_460_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Context(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Context(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Context(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Config_Cache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Context(builtin);
}
