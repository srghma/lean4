// Lean compiler output
// Module: Init.Data.List.MapIdx
// Imports: Init.Data.Option.Attach Init.Data.List.OfFn Init.ByCases Init.Data.Array.Bootstrap Init.Data.List.Nat.Range Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.TakeDrop Init.Data.Prod Init.Data.Subtype.Basic Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::List::Nat::Range::{
    initialize_Init_Data_List_Nat_Range, runtime_initialize_Init_Data_List_Nat_Range,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::OfFn::{
    initialize_Init_Data_List_OfFn, runtime_initialize_Init_Data_List_OfFn,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Option::Attach::{
    initialize_Init_Data_Option_Attach, runtime_initialize_Init_Data_Option_Attach,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub static l_List_mapFinIdx___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_List_mapFinIdx___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_mapFinIdx___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_List_mapFinIdx_go___redArg(
    mut v_f_229_: *mut LeanObject,
    mut v_bs_230_: *mut LeanObject,
    mut v_acc_231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_bs_230_) == 0 {
                    lean_dec(v_f_229_);
                    v___x_232_ = lean_array_to_list(v_acc_231_);
                    return v___x_232_;
                } else {
                    v_head_233_ = lean_ctor_get(v_bs_230_, 0);
                    lean_inc(v_head_233_);
                    v_tail_234_ = lean_ctor_get(v_bs_230_, 1);
                    lean_inc(v_tail_234_);
                    lean_dec_ref_known(v_bs_230_, 2);
                    v___x_235_ = lean_array_get_size(v_acc_231_);
                    lean_inc(v_f_229_);
                    v___x_236_ = lean_apply_3(v_f_229_, v___x_235_, v_head_233_, lean_box(0));
                    v___x_237_ = lean_array_push(v_acc_231_, v___x_236_);
                    v_bs_230_ = v_tail_234_;
                    v_acc_231_ = v___x_237_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapFinIdx_go(
    mut v_00_u03b1_239_: *mut LeanObject,
    mut v_00_u03b2_240_: *mut LeanObject,
    mut v_as_241_: *mut LeanObject,
    mut v_f_242_: *mut LeanObject,
    mut v_bs_243_: *mut LeanObject,
    mut v_acc_244_: *mut LeanObject,
    mut v_a_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    v___x_246_ = l_List_mapFinIdx_go___redArg(v_f_242_, v_bs_243_, v_acc_244_);
    return v___x_246_;
}
pub unsafe fn l_List_mapFinIdx_go___boxed(
    mut v_00_u03b1_247_: *mut LeanObject,
    mut v_00_u03b2_248_: *mut LeanObject,
    mut v_as_249_: *mut LeanObject,
    mut v_f_250_: *mut LeanObject,
    mut v_bs_251_: *mut LeanObject,
    mut v_acc_252_: *mut LeanObject,
    mut v_a_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_List_mapFinIdx_go(
        v_00_u03b1_247_,
        v_00_u03b2_248_,
        v_as_249_,
        v_f_250_,
        v_bs_251_,
        v_acc_252_,
        v_a_253_,
    );
    lean_dec(v_as_249_);
    return v_res_254_;
}
pub unsafe fn l_List_mapFinIdx___redArg(
    mut v_as_257_: *mut LeanObject,
    mut v_f_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_259_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_260_ = l_List_mapFinIdx_go___redArg(v_f_258_, v_as_257_, v___x_259_);
    return v___x_260_;
}
pub unsafe fn l_List_mapFinIdx(
    mut v_00_u03b1_261_: *mut LeanObject,
    mut v_00_u03b2_262_: *mut LeanObject,
    mut v_as_263_: *mut LeanObject,
    mut v_f_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_265_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_266_ = l_List_mapFinIdx_go___redArg(v_f_264_, v_as_263_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l_List_mapIdx_go___redArg(
    mut v_f_267_: *mut LeanObject,
    mut v_a_268_: *mut LeanObject,
    mut v_a_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_268_) == 0 {
                    lean_dec(v_f_267_);
                    v___x_270_ = lean_array_to_list(v_a_269_);
                    return v___x_270_;
                } else {
                    v_head_271_ = lean_ctor_get(v_a_268_, 0);
                    lean_inc(v_head_271_);
                    v_tail_272_ = lean_ctor_get(v_a_268_, 1);
                    lean_inc(v_tail_272_);
                    lean_dec_ref_known(v_a_268_, 2);
                    v___x_273_ = lean_array_get_size(v_a_269_);
                    lean_inc(v_f_267_);
                    v___x_274_ = lean_apply_2(v_f_267_, v___x_273_, v_head_271_);
                    v___x_275_ = lean_array_push(v_a_269_, v___x_274_);
                    v_a_268_ = v_tail_272_;
                    v_a_269_ = v___x_275_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapIdx_go(
    mut v_00_u03b1_277_: *mut LeanObject,
    mut v_00_u03b2_278_: *mut LeanObject,
    mut v_f_279_: *mut LeanObject,
    mut v_a_280_: *mut LeanObject,
    mut v_a_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    v___x_282_ = l_List_mapIdx_go___redArg(v_f_279_, v_a_280_, v_a_281_);
    return v___x_282_;
}
pub unsafe fn l_List_mapIdx___redArg(
    mut v_f_283_: *mut LeanObject,
    mut v_as_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_285_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_286_ = l_List_mapIdx_go___redArg(v_f_283_, v_as_284_, v___x_285_);
    return v___x_286_;
}
pub unsafe fn l_List_mapIdx(
    mut v_00_u03b1_287_: *mut LeanObject,
    mut v_00_u03b2_288_: *mut LeanObject,
    mut v_f_289_: *mut LeanObject,
    mut v_as_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_292_ = l_List_mapIdx_go___redArg(v_f_289_, v_as_290_, v___x_291_);
    return v___x_292_;
}
pub unsafe fn l_List_mapFinIdxM_go___redArg(
    mut v_inst_293_: *mut LeanObject,
    mut v_f_294_: *mut LeanObject,
    mut v_bs_295_: *mut LeanObject,
    mut v_acc_296_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_bs_295_) == 0 {
        let mut v_toApplicative_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_297_ = lean_ctor_get(v_inst_293_, 0);
        lean_inc_ref(v_toApplicative_297_);
        lean_dec(v_f_294_);
        lean_dec_ref(v_inst_293_);
        v_toPure_298_ = lean_ctor_get(v_toApplicative_297_, 1);
        lean_inc(v_toPure_298_);
        lean_dec_ref(v_toApplicative_297_);
        v___x_299_ = lean_array_to_list(v_acc_296_);
        v___x_300_ = lean_apply_2(v_toPure_298_, lean_box(0), v___x_299_);
        return v___x_300_;
    } else {
        let mut v_toBind_301_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_301_ = lean_ctor_get(v_inst_293_, 1);
        lean_inc(v_toBind_301_);
        v_head_302_ = lean_ctor_get(v_bs_295_, 0);
        lean_inc(v_head_302_);
        v_tail_303_ = lean_ctor_get(v_bs_295_, 1);
        lean_inc(v_tail_303_);
        lean_dec_ref_known(v_bs_295_, 2);
        lean_inc(v_f_294_);
        lean_inc_ref(v_acc_296_);
        v___f_304_ = lean_alloc_closure(
            l_List_mapFinIdxM_go___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_304_, 0, v_acc_296_);
        lean_closure_set(v___f_304_, 1, v_inst_293_);
        lean_closure_set(v___f_304_, 2, v_f_294_);
        lean_closure_set(v___f_304_, 3, v_tail_303_);
        v___x_305_ = lean_array_get_size(v_acc_296_);
        lean_dec_ref(v_acc_296_);
        v___x_306_ = lean_apply_3(v_f_294_, v___x_305_, v_head_302_, lean_box(0));
        v___x_307_ = lean_apply_4(
            v_toBind_301_,
            lean_box(0),
            lean_box(0),
            v___x_306_,
            v___f_304_,
        );
        return v___x_307_;
    }
}
pub unsafe fn l_List_mapFinIdxM_go___redArg___lam__0(
    mut v_acc_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
    mut v_f_310_: *mut LeanObject,
    mut v_tail_311_: *mut LeanObject,
    mut v_____do__lift_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    v___x_313_ = lean_array_push(v_acc_308_, v_____do__lift_312_);
    v___x_314_ = l_List_mapFinIdxM_go___redArg(v_inst_309_, v_f_310_, v_tail_311_, v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_List_mapFinIdxM_go(
    mut v_m_315_: *mut LeanObject,
    mut v_00_u03b1_316_: *mut LeanObject,
    mut v_00_u03b2_317_: *mut LeanObject,
    mut v_inst_318_: *mut LeanObject,
    mut v_as_319_: *mut LeanObject,
    mut v_f_320_: *mut LeanObject,
    mut v_bs_321_: *mut LeanObject,
    mut v_acc_322_: *mut LeanObject,
    mut v_a_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = l_List_mapFinIdxM_go___redArg(v_inst_318_, v_f_320_, v_bs_321_, v_acc_322_);
    return v___x_324_;
}
pub unsafe fn l_List_mapFinIdxM_go___boxed(
    mut v_m_325_: *mut LeanObject,
    mut v_00_u03b1_326_: *mut LeanObject,
    mut v_00_u03b2_327_: *mut LeanObject,
    mut v_inst_328_: *mut LeanObject,
    mut v_as_329_: *mut LeanObject,
    mut v_f_330_: *mut LeanObject,
    mut v_bs_331_: *mut LeanObject,
    mut v_acc_332_: *mut LeanObject,
    mut v_a_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l_List_mapFinIdxM_go(
        v_m_325_,
        v_00_u03b1_326_,
        v_00_u03b2_327_,
        v_inst_328_,
        v_as_329_,
        v_f_330_,
        v_bs_331_,
        v_acc_332_,
        v_a_333_,
    );
    lean_dec(v_as_329_);
    return v_res_334_;
}
pub unsafe fn l_List_mapFinIdxM___redArg(
    mut v_inst_335_: *mut LeanObject,
    mut v_as_336_: *mut LeanObject,
    mut v_f_337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_338_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_339_ = l_List_mapFinIdxM_go___redArg(v_inst_335_, v_f_337_, v_as_336_, v___x_338_);
    return v___x_339_;
}
pub unsafe fn l_List_mapFinIdxM(
    mut v_m_340_: *mut LeanObject,
    mut v_00_u03b1_341_: *mut LeanObject,
    mut v_00_u03b2_342_: *mut LeanObject,
    mut v_inst_343_: *mut LeanObject,
    mut v_as_344_: *mut LeanObject,
    mut v_f_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    v___x_346_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_347_ = l_List_mapFinIdxM_go___redArg(v_inst_343_, v_f_345_, v_as_344_, v___x_346_);
    return v___x_347_;
}
pub unsafe fn l_List_mapIdxM_go___redArg(
    mut v_inst_348_: *mut LeanObject,
    mut v_f_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
    mut v_a_351_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_350_) == 0 {
        let mut v_toApplicative_352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_352_ = lean_ctor_get(v_inst_348_, 0);
        lean_inc_ref(v_toApplicative_352_);
        lean_dec(v_f_349_);
        lean_dec_ref(v_inst_348_);
        v_toPure_353_ = lean_ctor_get(v_toApplicative_352_, 1);
        lean_inc(v_toPure_353_);
        lean_dec_ref(v_toApplicative_352_);
        v___x_354_ = lean_array_to_list(v_a_351_);
        v___x_355_ = lean_apply_2(v_toPure_353_, lean_box(0), v___x_354_);
        return v___x_355_;
    } else {
        let mut v_toBind_356_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_357_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_356_ = lean_ctor_get(v_inst_348_, 1);
        lean_inc(v_toBind_356_);
        v_head_357_ = lean_ctor_get(v_a_350_, 0);
        lean_inc(v_head_357_);
        v_tail_358_ = lean_ctor_get(v_a_350_, 1);
        lean_inc(v_tail_358_);
        lean_dec_ref_known(v_a_350_, 2);
        lean_inc(v_f_349_);
        lean_inc_ref(v_a_351_);
        v___f_359_ = lean_alloc_closure(
            l_List_mapIdxM_go___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_359_, 0, v_a_351_);
        lean_closure_set(v___f_359_, 1, v_inst_348_);
        lean_closure_set(v___f_359_, 2, v_f_349_);
        lean_closure_set(v___f_359_, 3, v_tail_358_);
        v___x_360_ = lean_array_get_size(v_a_351_);
        lean_dec_ref(v_a_351_);
        v___x_361_ = lean_apply_2(v_f_349_, v___x_360_, v_head_357_);
        v___x_362_ = lean_apply_4(
            v_toBind_356_,
            lean_box(0),
            lean_box(0),
            v___x_361_,
            v___f_359_,
        );
        return v___x_362_;
    }
}
pub unsafe fn l_List_mapIdxM_go___redArg___lam__0(
    mut v_a_363_: *mut LeanObject,
    mut v_inst_364_: *mut LeanObject,
    mut v_f_365_: *mut LeanObject,
    mut v_tail_366_: *mut LeanObject,
    mut v_____do__lift_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = lean_array_push(v_a_363_, v_____do__lift_367_);
    v___x_369_ = l_List_mapIdxM_go___redArg(v_inst_364_, v_f_365_, v_tail_366_, v___x_368_);
    return v___x_369_;
}
pub unsafe fn l_List_mapIdxM_go(
    mut v_m_370_: *mut LeanObject,
    mut v_00_u03b1_371_: *mut LeanObject,
    mut v_00_u03b2_372_: *mut LeanObject,
    mut v_inst_373_: *mut LeanObject,
    mut v_f_374_: *mut LeanObject,
    mut v_a_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = l_List_mapIdxM_go___redArg(v_inst_373_, v_f_374_, v_a_375_, v_a_376_);
    return v___x_377_;
}
pub unsafe fn l_List_mapIdxM___redArg(
    mut v_inst_378_: *mut LeanObject,
    mut v_f_379_: *mut LeanObject,
    mut v_as_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v___x_381_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_382_ = l_List_mapIdxM_go___redArg(v_inst_378_, v_f_379_, v_as_380_, v___x_381_);
    return v___x_382_;
}
pub unsafe fn l_List_mapIdxM(
    mut v_m_383_: *mut LeanObject,
    mut v_00_u03b1_384_: *mut LeanObject,
    mut v_00_u03b2_385_: *mut LeanObject,
    mut v_inst_386_: *mut LeanObject,
    mut v_f_387_: *mut LeanObject,
    mut v_as_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = l_List_mapFinIdx___redArg___closed__0;
    v___x_390_ = l_List_mapIdxM_go___redArg(v_inst_386_, v_f_387_, v_as_388_, v___x_389_);
    return v___x_390_;
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(
    mut v_x_391_: *mut LeanObject,
    mut v_x_392_: *mut LeanObject,
    mut v_h__1_393_: *mut LeanObject,
    mut v_h__2_394_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_391_) == 0 {
        let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_394_);
        v___x_395_ = lean_apply_2(v_h__1_393_, v_x_392_, lean_box(0));
        return v___x_395_;
    } else {
        let mut v_head_396_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_397_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_393_);
        v_head_396_ = lean_ctor_get(v_x_391_, 0);
        lean_inc(v_head_396_);
        v_tail_397_ = lean_ctor_get(v_x_391_, 1);
        lean_inc(v_tail_397_);
        lean_dec_ref_known(v_x_391_, 2);
        v___x_398_ = lean_apply_4(v_h__2_394_, v_head_396_, v_tail_397_, v_x_392_, lean_box(0));
        return v___x_398_;
    }
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter(
    mut v_00_u03b1_399_: *mut LeanObject,
    mut v_00_u03b2_400_: *mut LeanObject,
    mut v_as_401_: *mut LeanObject,
    mut v_motive_402_: *mut LeanObject,
    mut v_x_403_: *mut LeanObject,
    mut v_x_404_: *mut LeanObject,
    mut v_x_405_: *mut LeanObject,
    mut v_h__1_406_: *mut LeanObject,
    mut v_h__2_407_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_403_) == 0 {
        let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_407_);
        v___x_408_ = lean_apply_2(v_h__1_406_, v_x_404_, lean_box(0));
        return v___x_408_;
    } else {
        let mut v_head_409_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_406_);
        v_head_409_ = lean_ctor_get(v_x_403_, 0);
        lean_inc(v_head_409_);
        v_tail_410_ = lean_ctor_get(v_x_403_, 1);
        lean_inc(v_tail_410_);
        lean_dec_ref_known(v_x_403_, 2);
        v___x_411_ = lean_apply_4(v_h__2_407_, v_head_409_, v_tail_410_, v_x_404_, lean_box(0));
        return v___x_411_;
    }
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(
    mut v_00_u03b1_412_: *mut LeanObject,
    mut v_00_u03b2_413_: *mut LeanObject,
    mut v_as_414_: *mut LeanObject,
    mut v_motive_415_: *mut LeanObject,
    mut v_x_416_: *mut LeanObject,
    mut v_x_417_: *mut LeanObject,
    mut v_x_418_: *mut LeanObject,
    mut v_h__1_419_: *mut LeanObject,
    mut v_h__2_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_421_: *mut LeanObject = core::ptr::null_mut();
    v_res_421_ = l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter(
        v_00_u03b1_412_,
        v_00_u03b2_413_,
        v_as_414_,
        v_motive_415_,
        v_x_416_,
        v_x_417_,
        v_x_418_,
        v_h__1_419_,
        v_h__2_420_,
    );
    lean_dec(v_as_414_);
    return v_res_421_;
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(
    mut v_x_422_: *mut LeanObject,
    mut v_x_423_: *mut LeanObject,
    mut v_h__1_424_: *mut LeanObject,
    mut v_h__2_425_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_422_) == 0 {
        let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_425_);
        v___x_426_ = lean_apply_1(v_h__1_424_, v_x_423_);
        return v___x_426_;
    } else {
        let mut v_head_427_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_428_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_424_);
        v_head_427_ = lean_ctor_get(v_x_422_, 0);
        lean_inc(v_head_427_);
        v_tail_428_ = lean_ctor_get(v_x_422_, 1);
        lean_inc(v_tail_428_);
        lean_dec_ref_known(v_x_422_, 2);
        v___x_429_ = lean_apply_3(v_h__2_425_, v_head_427_, v_tail_428_, v_x_423_);
        return v___x_429_;
    }
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter(
    mut v_00_u03b1_430_: *mut LeanObject,
    mut v_00_u03b2_431_: *mut LeanObject,
    mut v_motive_432_: *mut LeanObject,
    mut v_x_433_: *mut LeanObject,
    mut v_x_434_: *mut LeanObject,
    mut v_h__1_435_: *mut LeanObject,
    mut v_h__2_436_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_433_) == 0 {
        let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_436_);
        v___x_437_ = lean_apply_1(v_h__1_435_, v_x_434_);
        return v___x_437_;
    } else {
        let mut v_head_438_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_435_);
        v_head_438_ = lean_ctor_get(v_x_433_, 0);
        lean_inc(v_head_438_);
        v_tail_439_ = lean_ctor_get(v_x_433_, 1);
        lean_inc(v_tail_439_);
        lean_dec_ref_known(v_x_433_, 2);
        v___x_440_ = lean_apply_3(v_h__2_436_, v_head_438_, v_tail_439_, v_x_434_);
        return v___x_440_;
    }
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter___redArg(
    mut v_opt_441_: *mut LeanObject,
    mut v_h__1_442_: *mut LeanObject,
    mut v_h__2_443_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_opt_441_) == 0 {
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_442_);
        v___x_444_ = lean_box(0);
        v___x_445_ = lean_apply_1(v_h__2_443_, v___x_444_);
        return v___x_445_;
    } else {
        let mut v_val_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_443_);
        v_val_446_ = lean_ctor_get(v_opt_441_, 0);
        lean_inc(v_val_446_);
        lean_dec_ref_known(v_opt_441_, 1);
        v___x_447_ = lean_apply_1(v_h__1_442_, v_val_446_);
        return v___x_447_;
    }
}
pub unsafe fn l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter(
    mut v_00_u03b1_448_: *mut LeanObject,
    mut v_motive_449_: *mut LeanObject,
    mut v_opt_450_: *mut LeanObject,
    mut v_h__1_451_: *mut LeanObject,
    mut v_h__2_452_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_opt_450_) == 0 {
        let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_451_);
        v___x_453_ = lean_box(0);
        v___x_454_ = lean_apply_1(v_h__2_452_, v___x_453_);
        return v___x_454_;
    } else {
        let mut v_val_455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_452_);
        v_val_455_ = lean_ctor_get(v_opt_450_, 0);
        lean_inc(v_val_455_);
        lean_dec_ref_known(v_opt_450_, 1);
        v___x_456_ = lean_apply_1(v_h__1_451_, v_val_455_);
        return v___x_456_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_MapIdx(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_OfFn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_MapIdx(builtin);
}
