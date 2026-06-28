// Lean compiler output
// Module: Std.Data.DTreeMap.AdditionalOperations
// Imports: Std.Data.DTreeMap.Raw.Basic Std.Data.DTreeMap.Internal.WF.Lemmas
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_filterMap___redArg, l_Std_DTreeMap_Internal_Impl_map___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg,
    l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg,
    l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg,
    l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg, l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::WF::Lemmas::{
    initialize_Std_Data_DTreeMap_Internal_WF_Lemmas,
    runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Basic::{
    initialize_Std_Data_DTreeMap_Raw_Basic, runtime_initialize_Std_Data_DTreeMap_Raw_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_DTreeMap_instCoeTypeForall__2(
    mut v_00_u03b1_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = lean_box(0);
    return v___x_182_;
}
pub unsafe fn l_Std_DTreeMap_filterMap___redArg(
    mut v_f_183_: *mut LeanObject,
    mut v_t_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
    v___x_185_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_183_, v_t_184_);
    return v___x_185_;
}
pub unsafe fn l_Std_DTreeMap_filterMap(
    mut v_00_u03b1_186_: *mut LeanObject,
    mut v_00_u03b2_187_: *mut LeanObject,
    mut v_00_u03b3_188_: *mut LeanObject,
    mut v_cmp_189_: *mut LeanObject,
    mut v_f_190_: *mut LeanObject,
    mut v_t_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Std_DTreeMap_Internal_Impl_filterMap___redArg(v_f_190_, v_t_191_);
    return v___x_192_;
}
pub unsafe fn l_Std_DTreeMap_filterMap___boxed(
    mut v_00_u03b1_193_: *mut LeanObject,
    mut v_00_u03b2_194_: *mut LeanObject,
    mut v_00_u03b3_195_: *mut LeanObject,
    mut v_cmp_196_: *mut LeanObject,
    mut v_f_197_: *mut LeanObject,
    mut v_t_198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_199_: *mut LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Std_DTreeMap_filterMap(
        v_00_u03b1_193_,
        v_00_u03b2_194_,
        v_00_u03b3_195_,
        v_cmp_196_,
        v_f_197_,
        v_t_198_,
    );
    lean_dec_ref(v_cmp_196_);
    return v_res_199_;
}
pub unsafe fn l_Std_DTreeMap_map___redArg(
    mut v_f_200_: *mut LeanObject,
    mut v_t_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    v___x_202_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_200_, v_t_201_);
    return v___x_202_;
}
pub unsafe fn l_Std_DTreeMap_map(
    mut v_00_u03b1_203_: *mut LeanObject,
    mut v_00_u03b2_204_: *mut LeanObject,
    mut v_00_u03b3_205_: *mut LeanObject,
    mut v_cmp_206_: *mut LeanObject,
    mut v_f_207_: *mut LeanObject,
    mut v_t_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    v___x_209_ = l_Std_DTreeMap_Internal_Impl_map___redArg(v_f_207_, v_t_208_);
    return v___x_209_;
}
pub unsafe fn l_Std_DTreeMap_map___boxed(
    mut v_00_u03b1_210_: *mut LeanObject,
    mut v_00_u03b2_211_: *mut LeanObject,
    mut v_00_u03b3_212_: *mut LeanObject,
    mut v_cmp_213_: *mut LeanObject,
    mut v_f_214_: *mut LeanObject,
    mut v_t_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_DTreeMap_map(
        v_00_u03b1_210_,
        v_00_u03b2_211_,
        v_00_u03b3_212_,
        v_cmp_213_,
        v_f_214_,
        v_t_215_,
    );
    lean_dec_ref(v_cmp_213_);
    return v_res_216_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE___redArg(
    mut v_cmp_217_: *mut LeanObject,
    mut v_t_218_: *mut LeanObject,
    mut v_k_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_220_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_217_, v_k_219_, v_t_218_);
    return v___x_220_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGE(
    mut v_00_u03b1_221_: *mut LeanObject,
    mut v_00_u03b2_222_: *mut LeanObject,
    mut v_cmp_223_: *mut LeanObject,
    mut v_inst_224_: *mut LeanObject,
    mut v_t_225_: *mut LeanObject,
    mut v_k_226_: *mut LeanObject,
    mut v_h_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_228_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_cmp_223_, v_k_226_, v_t_225_);
    return v___x_228_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT___redArg(
    mut v_cmp_229_: *mut LeanObject,
    mut v_t_230_: *mut LeanObject,
    mut v_k_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_232_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_229_, v_k_231_, v_t_230_);
    return v___x_232_;
}
pub unsafe fn l_Std_DTreeMap_getEntryGT(
    mut v_00_u03b1_233_: *mut LeanObject,
    mut v_00_u03b2_234_: *mut LeanObject,
    mut v_cmp_235_: *mut LeanObject,
    mut v_inst_236_: *mut LeanObject,
    mut v_t_237_: *mut LeanObject,
    mut v_k_238_: *mut LeanObject,
    mut v_h_239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    v___x_240_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_cmp_235_, v_k_238_, v_t_237_);
    return v___x_240_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE___redArg(
    mut v_cmp_241_: *mut LeanObject,
    mut v_t_242_: *mut LeanObject,
    mut v_k_243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    v___x_244_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_241_, v_k_243_, v_t_242_);
    return v___x_244_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLE(
    mut v_00_u03b1_245_: *mut LeanObject,
    mut v_00_u03b2_246_: *mut LeanObject,
    mut v_cmp_247_: *mut LeanObject,
    mut v_inst_248_: *mut LeanObject,
    mut v_t_249_: *mut LeanObject,
    mut v_k_250_: *mut LeanObject,
    mut v_h_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_cmp_247_, v_k_250_, v_t_249_);
    return v___x_252_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT___redArg(
    mut v_cmp_253_: *mut LeanObject,
    mut v_t_254_: *mut LeanObject,
    mut v_k_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_253_, v_k_255_, v_t_254_);
    return v___x_256_;
}
pub unsafe fn l_Std_DTreeMap_getEntryLT(
    mut v_00_u03b1_257_: *mut LeanObject,
    mut v_00_u03b2_258_: *mut LeanObject,
    mut v_cmp_259_: *mut LeanObject,
    mut v_inst_260_: *mut LeanObject,
    mut v_t_261_: *mut LeanObject,
    mut v_k_262_: *mut LeanObject,
    mut v_h_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_cmp_259_, v_k_262_, v_t_261_);
    return v___x_264_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE___redArg(
    mut v_cmp_265_: *mut LeanObject,
    mut v_t_266_: *mut LeanObject,
    mut v_k_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    v___x_268_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_265_, v_k_267_, v_t_266_);
    return v___x_268_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGE(
    mut v_00_u03b1_269_: *mut LeanObject,
    mut v_00_u03b2_270_: *mut LeanObject,
    mut v_cmp_271_: *mut LeanObject,
    mut v_inst_272_: *mut LeanObject,
    mut v_t_273_: *mut LeanObject,
    mut v_k_274_: *mut LeanObject,
    mut v_h_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    v___x_276_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_cmp_271_, v_k_274_, v_t_273_);
    return v___x_276_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT___redArg(
    mut v_cmp_277_: *mut LeanObject,
    mut v_t_278_: *mut LeanObject,
    mut v_k_279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    v___x_280_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_277_, v_k_279_, v_t_278_);
    return v___x_280_;
}
pub unsafe fn l_Std_DTreeMap_getKeyGT(
    mut v_00_u03b1_281_: *mut LeanObject,
    mut v_00_u03b2_282_: *mut LeanObject,
    mut v_cmp_283_: *mut LeanObject,
    mut v_inst_284_: *mut LeanObject,
    mut v_t_285_: *mut LeanObject,
    mut v_k_286_: *mut LeanObject,
    mut v_h_287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    v___x_288_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_cmp_283_, v_k_286_, v_t_285_);
    return v___x_288_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE___redArg(
    mut v_cmp_289_: *mut LeanObject,
    mut v_t_290_: *mut LeanObject,
    mut v_k_291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    v___x_292_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_289_, v_k_291_, v_t_290_);
    return v___x_292_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLE(
    mut v_00_u03b1_293_: *mut LeanObject,
    mut v_00_u03b2_294_: *mut LeanObject,
    mut v_cmp_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_t_297_: *mut LeanObject,
    mut v_k_298_: *mut LeanObject,
    mut v_h_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    v___x_300_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_cmp_295_, v_k_298_, v_t_297_);
    return v___x_300_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT___redArg(
    mut v_cmp_301_: *mut LeanObject,
    mut v_t_302_: *mut LeanObject,
    mut v_k_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v___x_304_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_301_, v_k_303_, v_t_302_);
    return v___x_304_;
}
pub unsafe fn l_Std_DTreeMap_getKeyLT(
    mut v_00_u03b1_305_: *mut LeanObject,
    mut v_00_u03b2_306_: *mut LeanObject,
    mut v_cmp_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
    mut v_t_309_: *mut LeanObject,
    mut v_k_310_: *mut LeanObject,
    mut v_h_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_cmp_307_, v_k_310_, v_t_309_);
    return v___x_312_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE___redArg(
    mut v_cmp_313_: *mut LeanObject,
    mut v_t_314_: *mut LeanObject,
    mut v_k_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    v___x_316_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_313_, v_k_315_, v_t_314_);
    return v___x_316_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGE(
    mut v_00_u03b1_317_: *mut LeanObject,
    mut v_cmp_318_: *mut LeanObject,
    mut v_00_u03b2_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
    mut v_t_321_: *mut LeanObject,
    mut v_k_322_: *mut LeanObject,
    mut v_h_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_cmp_318_, v_k_322_, v_t_321_);
    return v___x_324_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT___redArg(
    mut v_cmp_325_: *mut LeanObject,
    mut v_t_326_: *mut LeanObject,
    mut v_k_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    v___x_328_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_325_, v_k_327_, v_t_326_);
    return v___x_328_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryGT(
    mut v_00_u03b1_329_: *mut LeanObject,
    mut v_cmp_330_: *mut LeanObject,
    mut v_00_u03b2_331_: *mut LeanObject,
    mut v_inst_332_: *mut LeanObject,
    mut v_t_333_: *mut LeanObject,
    mut v_k_334_: *mut LeanObject,
    mut v_h_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_336_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_cmp_330_, v_k_334_, v_t_333_);
    return v___x_336_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE___redArg(
    mut v_cmp_337_: *mut LeanObject,
    mut v_t_338_: *mut LeanObject,
    mut v_k_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_337_, v_k_339_, v_t_338_);
    return v___x_340_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLE(
    mut v_00_u03b1_341_: *mut LeanObject,
    mut v_cmp_342_: *mut LeanObject,
    mut v_00_u03b2_343_: *mut LeanObject,
    mut v_inst_344_: *mut LeanObject,
    mut v_t_345_: *mut LeanObject,
    mut v_k_346_: *mut LeanObject,
    mut v_h_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    v___x_348_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_cmp_342_, v_k_346_, v_t_345_);
    return v___x_348_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT___redArg(
    mut v_cmp_349_: *mut LeanObject,
    mut v_t_350_: *mut LeanObject,
    mut v_k_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    v___x_352_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_349_, v_k_351_, v_t_350_);
    return v___x_352_;
}
pub unsafe fn l_Std_DTreeMap_Const_getEntryLT(
    mut v_00_u03b1_353_: *mut LeanObject,
    mut v_cmp_354_: *mut LeanObject,
    mut v_00_u03b2_355_: *mut LeanObject,
    mut v_inst_356_: *mut LeanObject,
    mut v_t_357_: *mut LeanObject,
    mut v_k_358_: *mut LeanObject,
    mut v_h_359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    v___x_360_ =
        l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_cmp_354_, v_k_358_, v_t_357_);
    return v___x_360_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_AdditionalOperations(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_AdditionalOperations(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Internal_WF_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
}
