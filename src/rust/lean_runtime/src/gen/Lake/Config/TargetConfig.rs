// Lean compiler output
// Module: Lake.Config.TargetConfig
// Imports: Lake.Build.Fetch Lake.Util.OpaqueType Lake.Util.OpaqueType
use crate::r#gen::Lake::Build::Fetch::{
    initialize_Lake_Build_Fetch, runtime_initialize_Lake_Build_Fetch,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_instInhabitedJobState_default;
use crate::r#gen::Lake::Config::OutFormat::l_Lake_formatQuery___boxed;
use crate::r#gen::Lake::Util::OpaqueType::{
    initialize_Lake_Util_OpaqueType, meta_initialize_Lake_Util_OpaqueType,
    runtime_initialize_Lake_Util_OpaqueType,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedTargetConfig_default___lam__0___closed__2_value: LeanStringObject<
    1,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instInhabitedTargetConfig_default___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedTargetConfig_default___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedTargetConfig_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedTargetConfig_default___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instInhabitedTargetConfig_default___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instInhabitedTargetConfig_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instInhabitedTargetConfig_default___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedTargetConfig_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedTargetConfig_default___closed__2_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v___x_188_ = l_Lake_instInhabitedJobState_default;
    v___x_189_ = lean_unsigned_to_nat(0);
    v___x_190_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_190_, 0, v___x_189_);
    lean_ctor_set(v___x_190_, 1, v___x_188_);
    return v___x_190_;
}
pub unsafe fn _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_191_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0_once),
        _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__0,
    );
    v___x_192_ = lean_task_pure(v___x_191_);
    return v___x_192_;
}
pub unsafe fn _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_194_: u8 = 0;
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    v___x_194_ = 0;
    v___x_195_ = l_Lake_instInhabitedTargetConfig_default___lam__0___closed__2;
    v___x_196_ = lean_box(0);
    v___x_197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1_once),
        _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__1,
    );
    v___x_198_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_198_, 0, v___x_197_);
    lean_ctor_set(v___x_198_, 1, v___x_196_);
    lean_ctor_set(v___x_198_, 2, v___x_195_);
    lean_ctor_set_uint8(
        v___x_198_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_194_,
    );
    return v___x_198_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default___lam__0(
    mut v_x_199_: *mut LeanObject,
    mut v___y_200_: *mut LeanObject,
    mut v___y_201_: *mut LeanObject,
    mut v___y_202_: *mut LeanObject,
    mut v___y_203_: *mut LeanObject,
    mut v___y_204_: *mut LeanObject,
    mut v___y_205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3_once),
        _init_l_Lake_instInhabitedTargetConfig_default___lam__0___closed__3,
    );
    v___x_208_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_208_, 0, v___x_207_);
    lean_ctor_set(v___x_208_, 1, v___y_205_);
    return v___x_208_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default___lam__0___boxed(
    mut v_x_209_: *mut LeanObject,
    mut v___y_210_: *mut LeanObject,
    mut v___y_211_: *mut LeanObject,
    mut v___y_212_: *mut LeanObject,
    mut v___y_213_: *mut LeanObject,
    mut v___y_214_: *mut LeanObject,
    mut v___y_215_: *mut LeanObject,
    mut v___y_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_217_: *mut LeanObject = core::ptr::null_mut();
    v_res_217_ = l_Lake_instInhabitedTargetConfig_default___lam__0(
        v_x_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_,
    );
    lean_dec_ref(v___y_214_);
    lean_dec(v___y_213_);
    lean_dec(v___y_212_);
    lean_dec(v___y_211_);
    lean_dec_ref(v___y_210_);
    lean_dec_ref(v_x_209_);
    return v_res_217_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default___lam__1(
    mut v_x_218_: u8,
    mut v___y_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_220_ = l_Lake_instInhabitedTargetConfig_default___lam__0___closed__2;
    return v___x_220_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default___lam__1___boxed(
    mut v_x_221_: *mut LeanObject,
    mut v___y_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_429__boxed_223_: u8 = 0;
    let mut v_res_224_: *mut LeanObject = core::ptr::null_mut();
    v_x_429__boxed_223_ = (lean_unbox(v_x_221_) as u8);
    v_res_224_ = l_Lake_instInhabitedTargetConfig_default___lam__1(v_x_429__boxed_223_, v___y_222_);
    lean_dec(v___y_222_);
    return v_res_224_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default(
    mut v_pkgName_230_: *mut LeanObject,
    mut v_name_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Lake_instInhabitedTargetConfig_default___closed__2;
    return v___x_232_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig_default___boxed(
    mut v_pkgName_233_: *mut LeanObject,
    mut v_name_234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_235_: *mut LeanObject = core::ptr::null_mut();
    v_res_235_ = l_Lake_instInhabitedTargetConfig_default(v_pkgName_233_, v_name_234_);
    lean_dec(v_name_234_);
    lean_dec(v_pkgName_233_);
    return v_res_235_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig(
    mut v_a_236_: *mut LeanObject,
    mut v_a_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    v___x_238_ = l_Lake_instInhabitedTargetConfig_default(v_a_236_, v_a_237_);
    return v___x_238_;
}
pub unsafe fn l_Lake_instInhabitedTargetConfig___boxed(
    mut v_a_239_: *mut LeanObject,
    mut v_a_240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_241_: *mut LeanObject = core::ptr::null_mut();
    v_res_241_ = l_Lake_instInhabitedTargetConfig(v_a_239_, v_a_240_);
    lean_dec(v_a_240_);
    lean_dec(v_a_239_);
    return v_res_241_;
}
pub unsafe fn l_Lake_mkTargetJobConfig___redArg(
    mut v_inst_242_: *mut LeanObject,
    mut v_fetch_243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    v___x_244_ = lean_alloc_closure(l_Lake_formatQuery___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_244_, 0, lean_box(0));
    lean_closure_set(v___x_244_, 1, v_inst_242_);
    v___x_245_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_245_, 0, v_fetch_243_);
    lean_ctor_set(v___x_245_, 1, v___x_244_);
    return v___x_245_;
}
pub unsafe fn l_Lake_mkTargetJobConfig(
    mut v_00_u03b1_246_: *mut LeanObject,
    mut v_pkgName_247_: *mut LeanObject,
    mut v_name_248_: *mut LeanObject,
    mut v_inst_249_: *mut LeanObject,
    mut v_h_250_: *mut LeanObject,
    mut v_fetch_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = lean_alloc_closure(l_Lake_formatQuery___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_252_, 0, lean_box(0));
    lean_closure_set(v___x_252_, 1, v_inst_249_);
    v___x_253_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_253_, 0, v_fetch_251_);
    lean_ctor_set(v___x_253_, 1, v___x_252_);
    return v___x_253_;
}
pub unsafe fn l_Lake_mkTargetJobConfig___boxed(
    mut v_00_u03b1_254_: *mut LeanObject,
    mut v_pkgName_255_: *mut LeanObject,
    mut v_name_256_: *mut LeanObject,
    mut v_inst_257_: *mut LeanObject,
    mut v_h_258_: *mut LeanObject,
    mut v_fetch_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_260_: *mut LeanObject = core::ptr::null_mut();
    v_res_260_ = l_Lake_mkTargetJobConfig(
        v_00_u03b1_254_,
        v_pkgName_255_,
        v_name_256_,
        v_inst_257_,
        v_h_258_,
        v_fetch_259_,
    );
    lean_dec(v_name_256_);
    lean_dec(v_pkgName_255_);
    return v_res_260_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk___redArg(
    mut v_a_261_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_261_);
    return v_a_261_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk___redArg___boxed(
    mut v_a_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_263_: *mut LeanObject = core::ptr::null_mut();
    v_res_263_ =
        l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk___redArg(v_a_262_);
    lean_dec_ref(v_a_262_);
    return v_res_263_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk(
    mut v_pkgName_264_: *mut LeanObject,
    mut v_name_265_: *mut LeanObject,
    mut v_a_266_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_a_266_);
    return v_a_266_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk___boxed(
    mut v_pkgName_267_: *mut LeanObject,
    mut v_name_268_: *mut LeanObject,
    mut v_a_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_270_: *mut LeanObject = core::ptr::null_mut();
    v_res_270_ = l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk(
        v_pkgName_267_,
        v_name_268_,
        v_a_269_,
    );
    lean_dec_ref(v_a_269_);
    lean_dec(v_name_268_);
    lean_dec(v_pkgName_267_);
    return v_res_270_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instCoeMk(
    mut v_pkgName_271_: *mut LeanObject,
    mut v_name_272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    v___x_273_ = lean_alloc_closure(
        l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeMk___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_273_, 0, v_pkgName_271_);
    lean_closure_set(v___x_273_, 1, v_name_272_);
    return v___x_273_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet___redArg(
    mut v_a_274_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_274_);
    return v_a_274_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet___redArg___boxed(
    mut v_a_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_276_: *mut LeanObject = core::ptr::null_mut();
    v_res_276_ = l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet___redArg(
        v_a_275_,
    );
    lean_dec(v_a_275_);
    return v_res_276_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet(
    mut v_pkgName_277_: *mut LeanObject,
    mut v_name_278_: *mut LeanObject,
    mut v_a_279_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_279_);
    return v_a_279_;
}
pub unsafe fn l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet___boxed(
    mut v_pkgName_280_: *mut LeanObject,
    mut v_name_281_: *mut LeanObject,
    mut v_a_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_283_: *mut LeanObject = core::ptr::null_mut();
    v_res_283_ = l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet(
        v_pkgName_280_,
        v_name_281_,
        v_a_282_,
    );
    lean_dec(v_a_282_);
    lean_dec(v_name_281_);
    lean_dec(v_pkgName_280_);
    return v_res_283_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instCoeGet(
    mut v_pkgName_284_: *mut LeanObject,
    mut v_name_285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_286_ = lean_alloc_closure(
        l___private_Lake_Config_TargetConfig_0__Lake_OpaqueTargetConfig_unsafeGet___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_286_, 0, v_pkgName_284_);
    lean_closure_set(v___x_286_, 1, v_name_285_);
    return v___x_286_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig___redArg(
    mut v_inst_287_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_inst_287_);
    return v_inst_287_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig___redArg___boxed(
    mut v_inst_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_289_: *mut LeanObject = core::ptr::null_mut();
    v_res_289_ = l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig___redArg(v_inst_288_);
    lean_dec_ref(v_inst_288_);
    return v_res_289_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig(
    mut v_pkgName_290_: *mut LeanObject,
    mut v_name_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_inst_292_);
    return v_inst_292_;
}
pub unsafe fn l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig___boxed(
    mut v_pkgName_293_: *mut LeanObject,
    mut v_name_294_: *mut LeanObject,
    mut v_inst_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_296_: *mut LeanObject = core::ptr::null_mut();
    v_res_296_ = l_Lake_OpaqueTargetConfig_instInhabitedOfTargetConfig(
        v_pkgName_293_,
        v_name_294_,
        v_inst_295_,
    );
    lean_dec_ref(v_inst_295_);
    lean_dec(v_name_294_);
    lean_dec(v_pkgName_293_);
    return v_res_296_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig___redArg(
    mut v_self_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_298_: *mut LeanObject = core::ptr::null_mut();
    v_config_298_ = lean_ctor_get(v_self_297_, 3);
    lean_inc(v_config_298_);
    return v_config_298_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig___redArg___boxed(
    mut v_self_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_300_: *mut LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Lake_NConfigDecl_targetConfig___redArg(v_self_299_);
    lean_dec_ref(v_self_299_);
    return v_res_300_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig(
    mut v_p_301_: *mut LeanObject,
    mut v_n_302_: *mut LeanObject,
    mut v_self_303_: *mut LeanObject,
    mut v_h_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_305_: *mut LeanObject = core::ptr::null_mut();
    v_config_305_ = lean_ctor_get(v_self_303_, 3);
    lean_inc(v_config_305_);
    return v_config_305_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig___boxed(
    mut v_p_306_: *mut LeanObject,
    mut v_n_307_: *mut LeanObject,
    mut v_self_308_: *mut LeanObject,
    mut v_h_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_310_: *mut LeanObject = core::ptr::null_mut();
    v_res_310_ = l_Lake_NConfigDecl_targetConfig(v_p_306_, v_n_307_, v_self_308_, v_h_309_);
    lean_dec_ref(v_self_308_);
    lean_dec(v_n_307_);
    lean_dec(v_p_306_);
    return v_res_310_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig_x3f___redArg(
    mut v_self_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    v_kind_312_ = lean_ctor_get(v_self_311_, 2);
    v_config_313_ = lean_ctor_get(v_self_311_, 3);
    v___x_314_ = l_Lean_Name_isAnonymous(v_kind_312_);
    if v___x_314_ == 0 {
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        v___x_315_ = lean_box(0);
        return v___x_315_;
    } else {
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_313_);
        v___x_316_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_316_, 0, v_config_313_);
        return v___x_316_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig_x3f___redArg___boxed(
    mut v_self_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_318_: *mut LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Lake_NConfigDecl_targetConfig_x3f___redArg(v_self_317_);
    lean_dec_ref(v_self_317_);
    return v_res_318_;
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig_x3f(
    mut v_p_319_: *mut LeanObject,
    mut v_n_320_: *mut LeanObject,
    mut v_self_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: u8 = 0;
    v_kind_322_ = lean_ctor_get(v_self_321_, 2);
    v_config_323_ = lean_ctor_get(v_self_321_, 3);
    v___x_324_ = l_Lean_Name_isAnonymous(v_kind_322_);
    if v___x_324_ == 0 {
        let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
        v___x_325_ = lean_box(0);
        return v___x_325_;
    } else {
        let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_config_323_);
        v___x_326_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_326_, 0, v_config_323_);
        return v___x_326_;
    }
}
pub unsafe fn l_Lake_NConfigDecl_targetConfig_x3f___boxed(
    mut v_p_327_: *mut LeanObject,
    mut v_n_328_: *mut LeanObject,
    mut v_self_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_330_: *mut LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Lake_NConfigDecl_targetConfig_x3f(v_p_327_, v_n_328_, v_self_329_);
    lean_dec_ref(v_self_329_);
    lean_dec(v_n_328_);
    lean_dec(v_p_327_);
    return v_res_330_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___redArg(
    mut v_t_331_: *mut LeanObject,
    mut v_k_332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: u8 = 0;
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_331_) == 0 {
                    v_k_333_ = lean_ctor_get(v_t_331_, 1);
                    v_v_334_ = lean_ctor_get(v_t_331_, 2);
                    v_l_335_ = lean_ctor_get(v_t_331_, 3);
                    v_r_336_ = lean_ctor_get(v_t_331_, 4);
                    v___x_337_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_332_, v_k_333_);
                    match v___x_337_ {
                        0 => {
                            v_t_331_ = v_l_335_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_334_);
                            v___x_339_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_339_, 0, v_v_334_);
                            return v___x_339_;
                        }
                        _ => {
                            v_t_331_ = v_r_336_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_341_ = lean_box(0);
                    return v___x_341_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___redArg___boxed(
    mut v_t_342_: *mut LeanObject,
    mut v_k_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___redArg(v_t_342_, v_k_343_);
    lean_dec(v_k_343_);
    lean_dec(v_t_342_);
    return v_res_344_;
}
pub unsafe fn l_Lake_Package_findTargetConfig_x3f(
    mut v_name_345_: *mut LeanObject,
    mut v_self_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_targetDeclMap_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v_kind_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: u8 = 0;
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetDeclMap_347_ = lean_ctor_get(v_self_346_, 15);
                v___x_348_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___redArg(v_targetDeclMap_347_, v_name_345_);
                if lean_obj_tag(v___x_348_) == 0 {
                    v___x_349_ = lean_box(0);
                    return v___x_349_;
                } else {
                    v_val_350_ = lean_ctor_get(v___x_348_, 0);
                    v_isSharedCheck_361_ = (!lean_is_exclusive(v___x_348_)) as u8;
                    if v_isSharedCheck_361_ == 0 {
                        v___x_352_ = v___x_348_;
                        v_isShared_353_ = v_isSharedCheck_361_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_350_);
                        lean_dec(v___x_348_);
                        v___x_352_ = lean_box(0);
                        v_isShared_353_ = v_isSharedCheck_361_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_kind_354_ = lean_ctor_get(v_val_350_, 2);
                lean_inc(v_kind_354_);
                v_config_355_ = lean_ctor_get(v_val_350_, 3);
                lean_inc(v_config_355_);
                lean_dec(v_val_350_);
                v___x_356_ = l_Lean_Name_isAnonymous(v_kind_354_);
                lean_dec(v_kind_354_);
                if v___x_356_ == 0 {
                    lean_dec(v_config_355_);
                    lean_del_object(v___x_352_);
                    v___x_357_ = lean_box(0);
                    return v___x_357_;
                } else {
                    if v_isShared_353_ == 0 {
                        lean_ctor_set(v___x_352_, 0, v_config_355_);
                        v___x_359_ = v___x_352_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_360_, 0, v_config_355_);
                        v___x_359_ = v_reuseFailAlloc_360_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Package_findTargetConfig_x3f___boxed(
    mut v_name_362_: *mut LeanObject,
    mut v_self_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_364_: *mut LeanObject = core::ptr::null_mut();
    v_res_364_ = l_Lake_Package_findTargetConfig_x3f(v_name_362_, v_self_363_);
    lean_dec_ref(v_self_363_);
    lean_dec(v_name_362_);
    return v_res_364_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0(
    mut v_00_u03b2_365_: *mut LeanObject,
    mut v_inst_366_: *mut LeanObject,
    mut v_t_367_: *mut LeanObject,
    mut v_k_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    v___x_369_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___redArg(v_t_367_, v_k_368_);
    return v___x_369_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0___boxed(
    mut v_00_u03b2_370_: *mut LeanObject,
    mut v_inst_371_: *mut LeanObject,
    mut v_t_372_: *mut LeanObject,
    mut v_k_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_374_: *mut LeanObject = core::ptr::null_mut();
    v_res_374_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_Package_findTargetConfig_x3f_spec__0(
            v_00_u03b2_370_,
            v_inst_371_,
            v_t_372_,
            v_k_373_,
        );
    lean_dec(v_k_373_);
    lean_dec(v_t_372_);
    return v_res_374_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_TargetConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_TargetConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_TargetConfig(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_OpaqueType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_TargetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Config_TargetConfig(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Config_TargetConfig(builtin);
}
