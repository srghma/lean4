// Lean compiler output
// Module: Init.ShareCommon
// Imports: Init.Data.UInt.Basic Init.Control.State
use crate::ffi::{
    lean_ptr_addr, lean_sharecommon_eq, lean_sharecommon_hash, lean_sharecommon_quick,
    lean_state_sharecommon, lean_usize_dec_eq, lean_usize_to_uint64,
};
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
pub static mut l_ShareCommon_StateFactoryPointed: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value:
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
    m_fun: l_ShareCommon_Object_ptrEq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value:
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
    m_fun: l_ShareCommon_Object_eq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value:
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
    m_fun: l_ShareCommon_Object_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_ShareCommon_StateFactory_mkImpl___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ShareCommon_StateFactory_mkImpl___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ShareCommon_StateFactory_mkImpl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ShareCommon_StateFactory_mkImpl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_ShareCommonT_run___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ShareCommonT_run___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ShareCommonT_run___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ShareCommonT_run___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_ShareCommon_Object_ptrEq(
    mut v_a_192_: *mut leanh::LeanObject,
    mut v_b_193_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_194_: usize = 0;
    let mut v___x_195_: usize = 0;
    let mut v___x_196_: u8 = 0;
    v___x_194_ = lean_ptr_addr(v_a_192_);
    v___x_195_ = lean_ptr_addr(v_b_193_);
    v___x_196_ = lean_usize_dec_eq(v___x_194_, v___x_195_);
    return v___x_196_;
}
pub unsafe fn l_ShareCommon_Object_ptrEq___boxed(
    mut v_a_197_: *mut leanh::LeanObject,
    mut v_b_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_199_: u8 = 0;
    let mut v_r_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_ShareCommon_Object_ptrEq(v_a_197_, v_b_198_);
    leanh::lean_dec(v_b_198_);
    leanh::lean_dec(v_a_197_);
    v_r_200_ = leanh::lean_box((v_res_199_) as usize);
    return v_r_200_;
}
pub unsafe fn l_ShareCommon_Object_ptrHash(mut v_a_201_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_202_: usize = 0;
    let mut v___x_203_: u64 = 0;
    v___x_202_ = lean_ptr_addr(v_a_201_);
    v___x_203_ = lean_usize_to_uint64(v___x_202_);
    return v___x_203_;
}
pub unsafe fn l_ShareCommon_Object_ptrHash___boxed(
    mut v_a_204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_205_: u64 = 0;
    let mut v_r_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_205_ = l_ShareCommon_Object_ptrHash(v_a_204_);
    leanh::lean_dec(v_a_204_);
    v_r_206_ = leanh::lean_box_uint64(v_res_205_);
    return v_r_206_;
}
pub unsafe fn _init_l_ShareCommon_StateFactoryPointed() -> *mut leanh::LeanObject {
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_207_ = leanh::lean_box(0);
    return v___x_207_;
}
pub unsafe fn l_ShareCommon_Object_eq___boxed(
    mut v_a_210_: *mut leanh::LeanObject,
    mut v_b_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_212_: u8 = 0;
    let mut v_r_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ = lean_sharecommon_eq(v_a_210_, v_b_211_);
    leanh::lean_dec(v_b_211_);
    leanh::lean_dec(v_a_210_);
    v_r_213_ = leanh::lean_box((v_res_212_) as usize);
    return v_r_213_;
}
pub unsafe fn l_ShareCommon_Object_hash___boxed(
    mut v_a_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: u64 = 0;
    let mut v_r_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = lean_sharecommon_hash(v_a_215_);
    leanh::lean_dec(v_a_215_);
    v_r_217_ = leanh::lean_box_uint64(v_res_216_);
    return v_r_217_;
}
pub unsafe fn l_ShareCommon_StateFactory_mkImpl___lam__0(
    mut v___y_218_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_219_: usize = 0;
    let mut v___x_220_: u64 = 0;
    v___x_219_ = lean_ptr_addr(v___y_218_);
    v___x_220_ = lean_usize_to_uint64(v___x_219_);
    return v___x_220_;
}
pub unsafe fn l_ShareCommon_StateFactory_mkImpl___lam__0___boxed(
    mut v___y_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: u64 = 0;
    let mut v_r_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_ShareCommon_StateFactory_mkImpl___lam__0(v___y_221_);
    leanh::lean_dec(v___y_221_);
    v_r_223_ = leanh::lean_box_uint64(v_res_222_);
    return v_r_223_;
}
pub unsafe fn l_ShareCommon_StateFactory_mkImpl___lam__2(
    mut v_mkMap_227_: *mut leanh::LeanObject,
    mut v___f_228_: *mut leanh::LeanObject,
    mut v_mkSet_229_: *mut leanh::LeanObject,
    mut v_x_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0;
    v___x_232_ = leanh::lean_unsigned_to_nat(1024);
    v___x_233_ = leanh::lean_apply_5(
        v_mkMap_227_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_231_,
        v___f_228_,
        v___x_232_,
    );
    v___x_234_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1;
    v___x_235_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2;
    v___x_236_ = leanh::lean_apply_4(
        v_mkSet_229_,
        leanh::lean_box(0),
        v___x_234_,
        v___x_235_,
        v___x_232_,
    );
    v___x_237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_237_, 0, v___x_233_);
    leanh::lean_ctor_set(v___x_237_, 1, v___x_236_);
    return v___x_237_;
}
pub unsafe fn l_ShareCommon_StateFactory_mkImpl(
    mut v_x_239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mkMap_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapFind_x3f_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapInsert_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mkSet_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_setFind_x3f_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_setInsert_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mkMap_240_ = leanh::lean_ctor_get(v_x_239_, 0);
    leanh::lean_inc(v_mkMap_240_);
    v_mapFind_x3f_241_ = leanh::lean_ctor_get(v_x_239_, 1);
    leanh::lean_inc_ref(v_mapFind_x3f_241_);
    v_mapInsert_242_ = leanh::lean_ctor_get(v_x_239_, 2);
    leanh::lean_inc(v_mapInsert_242_);
    v_mkSet_243_ = leanh::lean_ctor_get(v_x_239_, 3);
    leanh::lean_inc(v_mkSet_243_);
    v_setFind_x3f_244_ = leanh::lean_ctor_get(v_x_239_, 4);
    leanh::lean_inc_ref(v_setFind_x3f_244_);
    v_setInsert_245_ = leanh::lean_ctor_get(v_x_239_, 5);
    leanh::lean_inc(v_setInsert_245_);
    leanh::lean_dec_ref(v_x_239_);
    v___f_246_ = l_ShareCommon_StateFactory_mkImpl___closed__0;
    v___f_247_ = leanh::lean_alloc_closure(
        l_ShareCommon_StateFactory_mkImpl___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_247_, 0, v_mkMap_240_);
    leanh::lean_closure_set(v___f_247_, 1, v___f_246_);
    leanh::lean_closure_set(v___f_247_, 2, v_mkSet_243_);
    v___x_248_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0;
    v___x_249_ = leanh::lean_apply_4(
        v_mapFind_x3f_241_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_248_,
        v___f_246_,
    );
    v___x_250_ = leanh::lean_apply_4(
        v_mapInsert_242_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_248_,
        v___f_246_,
    );
    v___x_251_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1;
    v___x_252_ = l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2;
    v___x_253_ = leanh::lean_apply_3(
        v_setFind_x3f_244_,
        leanh::lean_box(0),
        v___x_251_,
        v___x_252_,
    );
    v___x_254_ = leanh::lean_apply_3(
        v_setInsert_245_,
        leanh::lean_box(0),
        v___x_251_,
        v___x_252_,
    );
    v___x_255_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_255_, 0, v___f_247_);
    leanh::lean_ctor_set(v___x_255_, 1, v___x_249_);
    leanh::lean_ctor_set(v___x_255_, 2, v___x_250_);
    leanh::lean_ctor_set(v___x_255_, 3, v___x_253_);
    leanh::lean_ctor_set(v___x_255_, 4, v___x_254_);
    return v___x_255_;
}
pub unsafe fn l_ShareCommon_StateFactory_get(
    mut v_a_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_256_);
    return v_a_256_;
}
pub unsafe fn l_ShareCommon_StateFactory_get___boxed(
    mut v_a_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_258_ = l_ShareCommon_StateFactory_get(v_a_257_);
    leanh::lean_dec(v_a_257_);
    return v_res_258_;
}
pub unsafe fn l_ShareCommon_StatePointed(
    mut v_00_u03c3_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = leanh::lean_box(0);
    return v___x_260_;
}
pub unsafe fn l_ShareCommon_StatePointed___boxed(
    mut v_00_u03c3_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = l_ShareCommon_StatePointed(v_00_u03c3_261_);
    leanh::lean_dec(v_00_u03c3_261_);
    return v_res_262_;
}
pub unsafe fn l_ShareCommon_mkStateImpl(
    mut v_00_u03c3_263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mkState_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mkState_264_ = leanh::lean_ctor_get(v_00_u03c3_263_, 0);
    leanh::lean_inc_ref(v_mkState_264_);
    leanh::lean_dec(v_00_u03c3_263_);
    v___x_265_ = leanh::lean_box(0);
    v___x_266_ = leanh::lean_apply_1(v_mkState_264_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l_ShareCommon_instInhabitedState(
    mut v_00_u03c3_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_ShareCommon_mkStateImpl(v_00_u03c3_267_);
    return v___x_268_;
}
pub unsafe fn l_ShareCommon_State_shareCommon___boxed(
    mut v_00_u03b1_273_: *mut leanh::LeanObject,
    mut v_00_u03c3_274_: *mut leanh::LeanObject,
    mut v_s_275_: *mut leanh::LeanObject,
    mut v_a_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = lean_state_sharecommon(v_00_u03c3_274_, v_s_275_, v_a_276_);
    leanh::lean_dec(v_00_u03c3_274_);
    return v_res_277_;
}
pub unsafe fn l_withShareCommon___redArg(
    mut v_self_278_: *mut leanh::LeanObject,
    mut v_a_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = leanh::lean_apply_2(v_self_278_, leanh::lean_box(0), v_a_279_);
    return v___x_280_;
}
pub unsafe fn l_withShareCommon(
    mut v_m_281_: *mut leanh::LeanObject,
    mut v_self_282_: *mut leanh::LeanObject,
    mut v_00_u03b1_283_: *mut leanh::LeanObject,
    mut v_a_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = leanh::lean_apply_2(v_self_282_, leanh::lean_box(0), v_a_284_);
    return v___x_285_;
}
pub unsafe fn l_shareCommonM___redArg(
    mut v_inst_286_: *mut leanh::LeanObject,
    mut v_a_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = leanh::lean_apply_2(v_inst_286_, leanh::lean_box(0), v_a_287_);
    return v___x_288_;
}
pub unsafe fn l_shareCommonM(
    mut v_m_289_: *mut leanh::LeanObject,
    mut v_00_u03b1_290_: *mut leanh::LeanObject,
    mut v_inst_291_: *mut leanh::LeanObject,
    mut v_a_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_293_ = leanh::lean_apply_2(v_inst_291_, leanh::lean_box(0), v_a_292_);
    return v___x_293_;
}
pub unsafe fn l_ShareCommonT_withShareCommon___redArg(
    mut v_00_u03c3_294_: *mut leanh::LeanObject,
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_a_296_: *mut leanh::LeanObject,
    mut v_a_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_298_ = leanh::lean_ctor_get(v_inst_295_, 0);
    leanh::lean_inc_ref(v_toApplicative_298_);
    leanh::lean_dec_ref(v_inst_295_);
    v_toPure_299_ = leanh::lean_ctor_get(v_toApplicative_298_, 1);
    leanh::lean_inc(v_toPure_299_);
    leanh::lean_dec_ref(v_toApplicative_298_);
    v___x_300_ = lean_state_sharecommon(v_00_u03c3_294_, v_a_297_, v_a_296_);
    v___x_301_ = leanh::lean_apply_2(v_toPure_299_, leanh::lean_box(0), v___x_300_);
    return v___x_301_;
}
pub unsafe fn l_ShareCommonT_withShareCommon___redArg___boxed(
    mut v_00_u03c3_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_a_304_: *mut leanh::LeanObject,
    mut v_a_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ =
        l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_302_, v_inst_303_, v_a_304_, v_a_305_);
    leanh::lean_dec(v_00_u03c3_302_);
    return v_res_306_;
}
pub unsafe fn l_ShareCommonT_withShareCommon(
    mut v_m_307_: *mut leanh::LeanObject,
    mut v_00_u03b1_308_: *mut leanh::LeanObject,
    mut v_00_u03c3_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
    mut v_a_311_: *mut leanh::LeanObject,
    mut v_a_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_313_ =
        l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_309_, v_inst_310_, v_a_311_, v_a_312_);
    return v___x_313_;
}
pub unsafe fn l_ShareCommonT_withShareCommon___boxed(
    mut v_m_314_: *mut leanh::LeanObject,
    mut v_00_u03b1_315_: *mut leanh::LeanObject,
    mut v_00_u03c3_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
    mut v_a_318_: *mut leanh::LeanObject,
    mut v_a_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_320_ = l_ShareCommonT_withShareCommon(
        v_m_314_,
        v_00_u03b1_315_,
        v_00_u03c3_316_,
        v_inst_317_,
        v_a_318_,
        v_a_319_,
    );
    leanh::lean_dec(v_00_u03c3_316_);
    return v_res_320_;
}
pub unsafe fn l_ShareCommonT_monadShareCommon___redArg___lam__0(
    mut v_00_u03c3_321_: *mut leanh::LeanObject,
    mut v_inst_322_: *mut leanh::LeanObject,
    mut v_00_u03b1_323_: *mut leanh::LeanObject,
    mut v___y_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_ShareCommonT_withShareCommon___redArg(
        v_00_u03c3_321_,
        v_inst_322_,
        v___y_324_,
        v___y_325_,
    );
    return v___x_326_;
}
pub unsafe fn l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(
    mut v_00_u03c3_327_: *mut leanh::LeanObject,
    mut v_inst_328_: *mut leanh::LeanObject,
    mut v_00_u03b1_329_: *mut leanh::LeanObject,
    mut v___y_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l_ShareCommonT_monadShareCommon___redArg___lam__0(
        v_00_u03c3_327_,
        v_inst_328_,
        v_00_u03b1_329_,
        v___y_330_,
        v___y_331_,
    );
    leanh::lean_dec(v_00_u03c3_327_);
    return v_res_332_;
}
pub unsafe fn l_ShareCommonT_monadShareCommon___redArg(
    mut v_00_u03c3_333_: *mut leanh::LeanObject,
    mut v_inst_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_335_ = leanh::lean_alloc_closure(
        l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_335_, 0, v_00_u03c3_333_);
    leanh::lean_closure_set(v___f_335_, 1, v_inst_334_);
    return v___f_335_;
}
pub unsafe fn l_ShareCommonT_monadShareCommon(
    mut v_m_336_: *mut leanh::LeanObject,
    mut v_00_u03c3_337_: *mut leanh::LeanObject,
    mut v_inst_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_339_ = leanh::lean_alloc_closure(
        l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_339_, 0, v_00_u03c3_337_);
    leanh::lean_closure_set(v___f_339_, 1, v_inst_338_);
    return v___f_339_;
}
pub unsafe fn l_ShareCommonT_run___redArg___lam__0(
    mut v_x_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_341_ = leanh::lean_ctor_get(v_x_340_, 0);
    leanh::lean_inc(v_fst_341_);
    return v_fst_341_;
}
pub unsafe fn l_ShareCommonT_run___redArg___lam__0___boxed(
    mut v_x_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_ShareCommonT_run___redArg___lam__0(v_x_342_);
    leanh::lean_dec_ref(v_x_342_);
    return v_res_343_;
}
pub unsafe fn l_ShareCommonT_run___redArg(
    mut v_00_u03c3_345_: *mut leanh::LeanObject,
    mut v_inst_346_: *mut leanh::LeanObject,
    mut v_x_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_348_ = leanh::lean_ctor_get(v_inst_346_, 0);
    leanh::lean_inc_ref(v_toApplicative_348_);
    leanh::lean_dec_ref(v_inst_346_);
    v_toFunctor_349_ = leanh::lean_ctor_get(v_toApplicative_348_, 0);
    leanh::lean_inc_ref(v_toFunctor_349_);
    leanh::lean_dec_ref(v_toApplicative_348_);
    v_map_350_ = leanh::lean_ctor_get(v_toFunctor_349_, 0);
    leanh::lean_inc(v_map_350_);
    leanh::lean_dec_ref(v_toFunctor_349_);
    v___f_351_ = l_ShareCommonT_run___redArg___closed__0;
    v___x_352_ = l_ShareCommon_mkStateImpl(v_00_u03c3_345_);
    v___x_353_ = leanh::lean_apply_1(v_x_347_, v___x_352_);
    v___x_354_ = leanh::lean_apply_4(
        v_map_350_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_351_,
        v___x_353_,
    );
    return v___x_354_;
}
pub unsafe fn l_ShareCommonT_run(
    mut v_m_355_: *mut leanh::LeanObject,
    mut v_00_u03c3_356_: *mut leanh::LeanObject,
    mut v_00_u03b1_357_: *mut leanh::LeanObject,
    mut v_inst_358_: *mut leanh::LeanObject,
    mut v_x_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_360_ = leanh::lean_ctor_get(v_inst_358_, 0);
    leanh::lean_inc_ref(v_toApplicative_360_);
    leanh::lean_dec_ref(v_inst_358_);
    v_toFunctor_361_ = leanh::lean_ctor_get(v_toApplicative_360_, 0);
    leanh::lean_inc_ref(v_toFunctor_361_);
    leanh::lean_dec_ref(v_toApplicative_360_);
    v_map_362_ = leanh::lean_ctor_get(v_toFunctor_361_, 0);
    leanh::lean_inc(v_map_362_);
    leanh::lean_dec_ref(v_toFunctor_361_);
    v___f_363_ = l_ShareCommonT_run___redArg___closed__0;
    v___x_364_ = l_ShareCommon_mkStateImpl(v_00_u03c3_356_);
    v___x_365_ = leanh::lean_apply_1(v_x_359_, v___x_364_);
    v___x_366_ = leanh::lean_apply_4(
        v_map_362_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_363_,
        v___x_365_,
    );
    return v___x_366_;
}
pub unsafe fn l_ShareCommonM_run___redArg(
    mut v_00_u03c3_367_: *mut leanh::LeanObject,
    mut v_x_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_369_ = l_ShareCommon_mkStateImpl(v_00_u03c3_367_);
    v___x_370_ = leanh::lean_apply_1(v_x_368_, v___x_369_);
    v_fst_371_ = leanh::lean_ctor_get(v___x_370_, 0);
    leanh::lean_inc(v_fst_371_);
    leanh::lean_dec_ref(v___x_370_);
    return v_fst_371_;
}
pub unsafe fn l_ShareCommonM_run(
    mut v_00_u03c3_372_: *mut leanh::LeanObject,
    mut v_00_u03b1_373_: *mut leanh::LeanObject,
    mut v_x_374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = l_ShareCommon_mkStateImpl(v_00_u03c3_372_);
    v___x_376_ = leanh::lean_apply_1(v_x_374_, v___x_375_);
    v_fst_377_ = leanh::lean_ctor_get(v___x_376_, 0);
    leanh::lean_inc(v_fst_377_);
    leanh::lean_dec_ref(v___x_376_);
    return v_fst_377_;
}
pub unsafe fn l_ShareCommon_shareCommon_x27___boxed(
    mut v_00_u03b1_380_: *mut leanh::LeanObject,
    mut v_a_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_382_ = lean_sharecommon_quick(v_a_381_);
    leanh::lean_dec(v_a_381_);
    return v_res_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_ShareCommon(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_ShareCommon_StateFactoryPointed = _init_l_ShareCommon_StateFactoryPointed();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_ShareCommon(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_ShareCommon(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_ShareCommon(builtin);
}