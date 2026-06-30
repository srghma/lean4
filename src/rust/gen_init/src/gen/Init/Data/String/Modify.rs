// Lean compiler output
// Module: Init.Data.String.Modify
// Imports: Init.Data.String.Termination Init.Data.ByteArray.Lemmas Init.Data.Char.Lemmas
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_string_utf8_byte_size, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_set, lean_uint32_add, lean_uint32_dec_le,
};
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::Char::Basic::{l_Char_toLower___boxed, l_Char_toUpper___boxed};
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Prelude::l_Char_utf8Size;
pub static l_String_toUpper___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_toUpper___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_toUpper___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_toUpper___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_toLower___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_toLower___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_toLower___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_toLower___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_String_Pos_set___boxed(
    mut v_s_227_: *mut leanh::LeanObject,
    mut v_p_228_: *mut leanh::LeanObject,
    mut v_c_229_: *mut leanh::LeanObject,
    mut v_hp_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_231_: u32 = 0;
    let mut v_res_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_231_ = leanh::lean_unbox_uint32(v_c_229_);
    leanh::lean_dec(v_c_229_);
    v_res_232_ = lean_string_utf8_set(v_s_227_, v_p_228_, v_c_boxed_231_);
    return v_res_232_;
}
pub unsafe fn l_String_Pos_toSetOfLE___redArg(
    mut v_q_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_q_233_);
    return v_q_233_;
}
pub unsafe fn l_String_Pos_toSetOfLE___redArg___boxed(
    mut v_q_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ = l_String_Pos_toSetOfLE___redArg(v_q_234_);
    leanh::lean_dec(v_q_234_);
    return v_res_235_;
}
pub unsafe fn l_String_Pos_toSetOfLE(
    mut v_s_236_: *mut leanh::LeanObject,
    mut v_q_237_: *mut leanh::LeanObject,
    mut v_p_238_: *mut leanh::LeanObject,
    mut v_c_239_: u32,
    mut v_hp_240_: *mut leanh::LeanObject,
    mut v_hpq_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_q_237_);
    return v_q_237_;
}
pub unsafe fn l_String_Pos_toSetOfLE___boxed(
    mut v_s_242_: *mut leanh::LeanObject,
    mut v_q_243_: *mut leanh::LeanObject,
    mut v_p_244_: *mut leanh::LeanObject,
    mut v_c_245_: *mut leanh::LeanObject,
    mut v_hp_246_: *mut leanh::LeanObject,
    mut v_hpq_247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_248_: u32 = 0;
    let mut v_res_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_248_ = leanh::lean_unbox_uint32(v_c_245_);
    leanh::lean_dec(v_c_245_);
    v_res_249_ = l_String_Pos_toSetOfLE(
        v_s_242_,
        v_q_243_,
        v_p_244_,
        v_c_boxed_248_,
        v_hp_246_,
        v_hpq_247_,
    );
    leanh::lean_dec(v_p_244_);
    leanh::lean_dec(v_q_243_);
    leanh::lean_dec_ref(v_s_242_);
    return v_res_249_;
}
pub unsafe fn l_String_Pos_pastSet___redArg(
    mut v_p_250_: *mut leanh::LeanObject,
    mut v_c_251_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Char_utf8Size(v_c_251_);
    v___x_253_ = lean_nat_add(v_p_250_, v___x_252_);
    leanh::lean_dec(v___x_252_);
    return v___x_253_;
}
pub unsafe fn l_String_Pos_pastSet___redArg___boxed(
    mut v_p_254_: *mut leanh::LeanObject,
    mut v_c_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_256_: u32 = 0;
    let mut v_res_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_256_ = leanh::lean_unbox_uint32(v_c_255_);
    leanh::lean_dec(v_c_255_);
    v_res_257_ = l_String_Pos_pastSet___redArg(v_p_254_, v_c_boxed_256_);
    leanh::lean_dec(v_p_254_);
    return v_res_257_;
}
pub unsafe fn l_String_Pos_pastSet(
    mut v_s_258_: *mut leanh::LeanObject,
    mut v_p_259_: *mut leanh::LeanObject,
    mut v_c_260_: u32,
    mut v_hp_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_262_ = l_Char_utf8Size(v_c_260_);
    v___x_263_ = lean_nat_add(v_p_259_, v___x_262_);
    leanh::lean_dec(v___x_262_);
    return v___x_263_;
}
pub unsafe fn l_String_Pos_pastSet___boxed(
    mut v_s_264_: *mut leanh::LeanObject,
    mut v_p_265_: *mut leanh::LeanObject,
    mut v_c_266_: *mut leanh::LeanObject,
    mut v_hp_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_268_: u32 = 0;
    let mut v_res_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_268_ = leanh::lean_unbox_uint32(v_c_266_);
    leanh::lean_dec(v_c_266_);
    v_res_269_ = l_String_Pos_pastSet(v_s_264_, v_p_265_, v_c_boxed_268_, v_hp_267_);
    leanh::lean_dec(v_p_265_);
    leanh::lean_dec_ref(v_s_264_);
    return v_res_269_;
}
pub unsafe fn l_String_Pos_appendRight___redArg(
    mut v_p_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_p_270_);
    return v_p_270_;
}
pub unsafe fn l_String_Pos_appendRight___redArg___boxed(
    mut v_p_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_272_ = l_String_Pos_appendRight___redArg(v_p_271_);
    leanh::lean_dec(v_p_271_);
    return v_res_272_;
}
pub unsafe fn l_String_Pos_appendRight(
    mut v_s_273_: *mut leanh::LeanObject,
    mut v_p_274_: *mut leanh::LeanObject,
    mut v_t_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_p_274_);
    return v_p_274_;
}
pub unsafe fn l_String_Pos_appendRight___boxed(
    mut v_s_276_: *mut leanh::LeanObject,
    mut v_p_277_: *mut leanh::LeanObject,
    mut v_t_278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_279_ = l_String_Pos_appendRight(v_s_276_, v_p_277_, v_t_278_);
    leanh::lean_dec_ref(v_t_278_);
    leanh::lean_dec(v_p_277_);
    leanh::lean_dec_ref(v_s_276_);
    return v_res_279_;
}
pub unsafe fn l_String_Pos_modify___redArg(
    mut v_s_280_: *mut leanh::LeanObject,
    mut v_p_281_: *mut leanh::LeanObject,
    mut v_f_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_283_: u32 = 0;
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u32 = 0;
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = lean_string_utf8_get_fast(v_s_280_, v_p_281_);
    v___x_284_ = leanh::lean_box_uint32(v___x_283_);
    v___x_285_ = leanh::lean_apply_1(v_f_282_, v___x_284_);
    v___x_286_ = leanh::lean_unbox_uint32(v___x_285_);
    leanh::lean_dec(v___x_285_);
    v___x_287_ = lean_string_utf8_set(v_s_280_, v_p_281_, v___x_286_);
    return v___x_287_;
}
pub unsafe fn l_String_Pos_modify(
    mut v_s_288_: *mut leanh::LeanObject,
    mut v_p_289_: *mut leanh::LeanObject,
    mut v_f_290_: *mut leanh::LeanObject,
    mut v_hp_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_292_: u32 = 0;
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: u32 = 0;
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = lean_string_utf8_get_fast(v_s_288_, v_p_289_);
    v___x_293_ = leanh::lean_box_uint32(v___x_292_);
    v___x_294_ = leanh::lean_apply_1(v_f_290_, v___x_293_);
    v___x_295_ = leanh::lean_unbox_uint32(v___x_294_);
    leanh::lean_dec(v___x_294_);
    v___x_296_ = lean_string_utf8_set(v_s_288_, v_p_289_, v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_String_Pos_toModifyOfLE___redArg(
    mut v_q_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_q_297_);
    return v_q_297_;
}
pub unsafe fn l_String_Pos_toModifyOfLE___redArg___boxed(
    mut v_q_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_299_ = l_String_Pos_toModifyOfLE___redArg(v_q_298_);
    leanh::lean_dec(v_q_298_);
    return v_res_299_;
}
pub unsafe fn l_String_Pos_toModifyOfLE(
    mut v_s_300_: *mut leanh::LeanObject,
    mut v_q_301_: *mut leanh::LeanObject,
    mut v_p_302_: *mut leanh::LeanObject,
    mut v_f_303_: *mut leanh::LeanObject,
    mut v_hp_304_: *mut leanh::LeanObject,
    mut v_hpq_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_q_301_);
    return v_q_301_;
}
pub unsafe fn l_String_Pos_toModifyOfLE___boxed(
    mut v_s_306_: *mut leanh::LeanObject,
    mut v_q_307_: *mut leanh::LeanObject,
    mut v_p_308_: *mut leanh::LeanObject,
    mut v_f_309_: *mut leanh::LeanObject,
    mut v_hp_310_: *mut leanh::LeanObject,
    mut v_hpq_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_String_Pos_toModifyOfLE(
        v_s_306_, v_q_307_, v_p_308_, v_f_309_, v_hp_310_, v_hpq_311_,
    );
    leanh::lean_dec_ref(v_f_309_);
    leanh::lean_dec(v_p_308_);
    leanh::lean_dec(v_q_307_);
    leanh::lean_dec_ref(v_s_306_);
    return v_res_312_;
}
pub unsafe fn l_String_Pos_pastModify___redArg(
    mut v_s_313_: *mut leanh::LeanObject,
    mut v_p_314_: *mut leanh::LeanObject,
    mut v_f_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_316_: u32 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: u32 = 0;
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = lean_string_utf8_get_fast(v_s_313_, v_p_314_);
    v___x_317_ = leanh::lean_box_uint32(v___x_316_);
    v___x_318_ = leanh::lean_apply_1(v_f_315_, v___x_317_);
    v___x_319_ = leanh::lean_unbox_uint32(v___x_318_);
    leanh::lean_dec(v___x_318_);
    v___x_320_ = l_Char_utf8Size(v___x_319_);
    v___x_321_ = lean_nat_add(v_p_314_, v___x_320_);
    leanh::lean_dec(v___x_320_);
    return v___x_321_;
}
pub unsafe fn l_String_Pos_pastModify___redArg___boxed(
    mut v_s_322_: *mut leanh::LeanObject,
    mut v_p_323_: *mut leanh::LeanObject,
    mut v_f_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = l_String_Pos_pastModify___redArg(v_s_322_, v_p_323_, v_f_324_);
    leanh::lean_dec(v_p_323_);
    leanh::lean_dec_ref(v_s_322_);
    return v_res_325_;
}
pub unsafe fn l_String_Pos_pastModify(
    mut v_s_326_: *mut leanh::LeanObject,
    mut v_p_327_: *mut leanh::LeanObject,
    mut v_f_328_: *mut leanh::LeanObject,
    mut v_hp_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_330_: u32 = 0;
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: u32 = 0;
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_330_ = lean_string_utf8_get_fast(v_s_326_, v_p_327_);
    v___x_331_ = leanh::lean_box_uint32(v___x_330_);
    v___x_332_ = leanh::lean_apply_1(v_f_328_, v___x_331_);
    v___x_333_ = leanh::lean_unbox_uint32(v___x_332_);
    leanh::lean_dec(v___x_332_);
    v___x_334_ = l_Char_utf8Size(v___x_333_);
    v___x_335_ = lean_nat_add(v_p_327_, v___x_334_);
    leanh::lean_dec(v___x_334_);
    return v___x_335_;
}
pub unsafe fn l_String_Pos_pastModify___boxed(
    mut v_s_336_: *mut leanh::LeanObject,
    mut v_p_337_: *mut leanh::LeanObject,
    mut v_f_338_: *mut leanh::LeanObject,
    mut v_hp_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_340_ = l_String_Pos_pastModify(v_s_336_, v_p_337_, v_f_338_, v_hp_339_);
    leanh::lean_dec(v_p_337_);
    leanh::lean_dec_ref(v_s_336_);
    return v_res_340_;
}
pub unsafe fn l_String_Pos_Raw_set___boxed(
    mut v_a_00___x40___internal___hyg_344_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_345_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_3__boxed_347_: u32 = 0;
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_3__boxed_347_ =
        leanh::lean_unbox_uint32(v_a_00___x40___internal___hyg_346_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_346_);
    v_res_348_ = lean_string_utf8_set(
        v_a_00___x40___internal___hyg_344_,
        v_a_00___x40___internal___hyg_345_,
        v_a_00___x40___internal___hyg_3__boxed_347_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_345_);
    return v_res_348_;
}
pub unsafe fn l_String_set___boxed(
    mut v_a_00___x40___internal___hyg_352_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_353_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_3__boxed_355_: u32 = 0;
    let mut v_res_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_3__boxed_355_ =
        leanh::lean_unbox_uint32(v_a_00___x40___internal___hyg_354_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_354_);
    v_res_356_ = lean_string_utf8_set(
        v_a_00___x40___internal___hyg_352_,
        v_a_00___x40___internal___hyg_353_,
        v_a_00___x40___internal___hyg_3__boxed_355_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_353_);
    return v_res_356_;
}
pub unsafe fn l_String_Pos_Raw_modify(
    mut v_s_357_: *mut leanh::LeanObject,
    mut v_i_358_: *mut leanh::LeanObject,
    mut v_f_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_360_: u32 = 0;
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: u32 = 0;
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = lean_string_utf8_get(v_s_357_, v_i_358_);
    v___x_361_ = leanh::lean_box_uint32(v___x_360_);
    v___x_362_ = leanh::lean_apply_1(v_f_359_, v___x_361_);
    v___x_363_ = leanh::lean_unbox_uint32(v___x_362_);
    leanh::lean_dec(v___x_362_);
    v___x_364_ = lean_string_utf8_set(v_s_357_, v_i_358_, v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_String_Pos_Raw_modify___boxed(
    mut v_s_365_: *mut leanh::LeanObject,
    mut v_i_366_: *mut leanh::LeanObject,
    mut v_f_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_String_Pos_Raw_modify(v_s_365_, v_i_366_, v_f_367_);
    leanh::lean_dec(v_i_366_);
    return v_res_368_;
}
pub unsafe fn l_String_modify(
    mut v_s_369_: *mut leanh::LeanObject,
    mut v_i_370_: *mut leanh::LeanObject,
    mut v_f_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_372_: u32 = 0;
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: u32 = 0;
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_string_utf8_get(v_s_369_, v_i_370_);
    v___x_373_ = leanh::lean_box_uint32(v___x_372_);
    v___x_374_ = leanh::lean_apply_1(v_f_371_, v___x_373_);
    v___x_375_ = leanh::lean_unbox_uint32(v___x_374_);
    leanh::lean_dec(v___x_374_);
    v___x_376_ = lean_string_utf8_set(v_s_369_, v_i_370_, v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_String_modify___boxed(
    mut v_s_377_: *mut leanh::LeanObject,
    mut v_i_378_: *mut leanh::LeanObject,
    mut v_f_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ = l_String_modify(v_s_377_, v_i_378_, v_f_379_);
    leanh::lean_dec(v_i_378_);
    return v_res_380_;
}
pub unsafe fn l_String_mapAux(
    mut v_f_381_: *mut leanh::LeanObject,
    mut v_s_382_: *mut leanh::LeanObject,
    mut v_p_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: u8 = 0;
    let mut v___x_386_: u32 = 0;
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: u32 = 0;
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: u32 = 0;
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_384_ = lean_string_utf8_byte_size(v_s_382_);
                v___x_385_ = lean_nat_dec_eq(v_p_383_, v___x_384_);
                if v___x_385_ == 0 {
                    v___x_386_ = lean_string_utf8_get_fast(v_s_382_, v_p_383_);
                    v___x_387_ = leanh::lean_box_uint32(v___x_386_);
                    leanh::lean_inc_ref(v_f_381_);
                    v___x_388_ = leanh::lean_apply_1(v_f_381_, v___x_387_);
                    v___x_389_ = leanh::lean_unbox_uint32(v___x_388_);
                    leanh::lean_inc(v_p_383_);
                    v___x_390_ = lean_string_utf8_set(v_s_382_, v_p_383_, v___x_389_);
                    v___x_391_ = leanh::lean_unbox_uint32(v___x_388_);
                    leanh::lean_dec(v___x_388_);
                    v___x_392_ = l_Char_utf8Size(v___x_391_);
                    v___x_393_ = lean_nat_add(v_p_383_, v___x_392_);
                    leanh::lean_dec(v___x_392_);
                    leanh::lean_dec(v_p_383_);
                    v_s_382_ = v___x_390_;
                    v_p_383_ = v___x_393_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_p_383_);
                    leanh::lean_dec_ref(v_f_381_);
                    return v_s_382_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_map(
    mut v_f_395_: *mut leanh::LeanObject,
    mut v_s_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = leanh::lean_unsigned_to_nat(0);
    v___x_398_ = l_String_mapAux(v_f_395_, v_s_396_, v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_String_toUpper(
    mut v_s_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l_String_toUpper___closed__0;
    v___x_402_ = leanh::lean_unsigned_to_nat(0);
    v___x_403_ = l_String_mapAux(v___x_401_, v_s_400_, v___x_402_);
    return v___x_403_;
}
pub unsafe fn l_String_toLower(
    mut v_s_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_406_ = l_String_toLower___closed__0;
    v___x_407_ = leanh::lean_unsigned_to_nat(0);
    v___x_408_ = l_String_mapAux(v___x_406_, v_s_405_, v___x_407_);
    return v___x_408_;
}
pub unsafe fn l_String_capitalize(
    mut v_s_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: u32 = 0;
    let mut v___x_412_: u32 = 0;
    let mut v___x_413_: u8 = 0;
    v___x_410_ = leanh::lean_unsigned_to_nat(0);
    v___x_411_ = lean_string_utf8_get(v_s_409_, v___x_410_);
    v___x_412_ = 97;
    v___x_413_ = lean_uint32_dec_le(v___x_412_, v___x_411_);
    if v___x_413_ == 0 {
        let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_414_ = lean_string_utf8_set(v_s_409_, v___x_410_, v___x_411_);
        return v___x_414_;
    } else {
        let mut v___x_415_: u32 = 0;
        let mut v___x_416_: u8 = 0;
        v___x_415_ = 122;
        v___x_416_ = lean_uint32_dec_le(v___x_411_, v___x_415_);
        if v___x_416_ == 0 {
            let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_417_ = lean_string_utf8_set(v_s_409_, v___x_410_, v___x_411_);
            return v___x_417_;
        } else {
            let mut v___x_418_: u32 = 0;
            let mut v___x_419_: u32 = 0;
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_418_ = 4294967264;
            v___x_419_ = lean_uint32_add(v___x_411_, v___x_418_);
            v___x_420_ = lean_string_utf8_set(v_s_409_, v___x_410_, v___x_419_);
            return v___x_420_;
        }
    }
}
pub unsafe fn lean_string_capitalize(
    mut v_s_421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u32 = 0;
    let mut v___x_424_: u32 = 0;
    let mut v___x_425_: u8 = 0;
    v___x_422_ = leanh::lean_unsigned_to_nat(0);
    v___x_423_ = lean_string_utf8_get(v_s_421_, v___x_422_);
    v___x_424_ = 97;
    v___x_425_ = lean_uint32_dec_le(v___x_424_, v___x_423_);
    if v___x_425_ == 0 {
        let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_426_ = lean_string_utf8_set(v_s_421_, v___x_422_, v___x_423_);
        return v___x_426_;
    } else {
        let mut v___x_427_: u32 = 0;
        let mut v___x_428_: u8 = 0;
        v___x_427_ = 122;
        v___x_428_ = lean_uint32_dec_le(v___x_423_, v___x_427_);
        if v___x_428_ == 0 {
            let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_429_ = lean_string_utf8_set(v_s_421_, v___x_422_, v___x_423_);
            return v___x_429_;
        } else {
            let mut v___x_430_: u32 = 0;
            let mut v___x_431_: u32 = 0;
            let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_430_ = 4294967264;
            v___x_431_ = lean_uint32_add(v___x_423_, v___x_430_);
            v___x_432_ = lean_string_utf8_set(v_s_421_, v___x_422_, v___x_431_);
            return v___x_432_;
        }
    }
}
pub unsafe fn l_String_decapitalize(
    mut v_s_433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: u32 = 0;
    let mut v___x_436_: u32 = 0;
    let mut v___x_437_: u8 = 0;
    v___x_434_ = leanh::lean_unsigned_to_nat(0);
    v___x_435_ = lean_string_utf8_get(v_s_433_, v___x_434_);
    v___x_436_ = 65;
    v___x_437_ = lean_uint32_dec_le(v___x_436_, v___x_435_);
    if v___x_437_ == 0 {
        let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_438_ = lean_string_utf8_set(v_s_433_, v___x_434_, v___x_435_);
        return v___x_438_;
    } else {
        let mut v___x_439_: u32 = 0;
        let mut v___x_440_: u8 = 0;
        v___x_439_ = 90;
        v___x_440_ = lean_uint32_dec_le(v___x_435_, v___x_439_);
        if v___x_440_ == 0 {
            let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_441_ = lean_string_utf8_set(v_s_433_, v___x_434_, v___x_435_);
            return v___x_441_;
        } else {
            let mut v___x_442_: u32 = 0;
            let mut v___x_443_: u32 = 0;
            let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_442_ = 32;
            v___x_443_ = lean_uint32_add(v___x_435_, v___x_442_);
            v___x_444_ = lean_string_utf8_set(v_s_433_, v___x_434_, v___x_443_);
            return v___x_444_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Modify(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Modify(
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
pub unsafe fn initialize_Init_Data_String_Modify(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Modify(builtin);
}