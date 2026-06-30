// Lean compiler output
// Module: Init.Util
// Imports: Init.Data.ToString.Basic
use crate::ffi::{
    lean_dbg_sleep, lean_dbg_stack_trace, lean_dbg_trace, lean_dbg_trace_if_shared,
    lean_is_exclusive_obj, lean_ptr_addr, lean_string_append, lean_usize_dec_eq,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Prelude::l_panic___redArg;
pub static l_mkPanicMessage___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [80, 65, 78, 73, 67, 32, 97, 116, 32, 0],
    };
static mut l_mkPanicMessage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkPanicMessage___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkPanicMessage___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_mkPanicMessage___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkPanicMessage___closed__1_value) as *mut leanh::LeanObject;
pub static l_mkPanicMessage___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_mkPanicMessage___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkPanicMessage___closed__2_value) as *mut leanh::LeanObject;
pub static l_mkPanicMessageWithDecl___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_mkPanicMessageWithDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkPanicMessageWithDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_dbgTrace___boxed(
    mut v_00_u03b1_316_: *mut leanh::LeanObject,
    mut v_s_317_: *mut leanh::LeanObject,
    mut v_f_318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = lean_dbg_trace(v_s_317_, v_f_318_);
    return v_res_319_;
}
pub unsafe fn l_dbgTraceVal___redArg___lam__0(
    mut v_a_320_: *mut leanh::LeanObject,
    mut v_x_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_320_);
    return v_a_320_;
}
pub unsafe fn l_dbgTraceVal___redArg___lam__0___boxed(
    mut v_a_322_: *mut leanh::LeanObject,
    mut v_x_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_dbgTraceVal___redArg___lam__0(v_a_322_, v_x_323_);
    leanh::lean_dec(v_a_322_);
    return v_res_324_;
}
pub unsafe fn l_dbgTraceVal___redArg(
    mut v_inst_325_: *mut leanh::LeanObject,
    mut v_a_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_326_);
    v___f_327_ = leanh::lean_alloc_closure(
        l_dbgTraceVal___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_327_, 0, v_a_326_);
    v___x_328_ = leanh::lean_apply_1(v_inst_325_, v_a_326_);
    v___x_329_ = lean_dbg_trace(v___x_328_, v___f_327_);
    return v___x_329_;
}
pub unsafe fn l_dbgTraceVal(
    mut v_00_u03b1_330_: *mut leanh::LeanObject,
    mut v_inst_331_: *mut leanh::LeanObject,
    mut v_a_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = l_dbgTraceVal___redArg(v_inst_331_, v_a_332_);
    return v___x_333_;
}
pub unsafe fn l_dbgTraceIfShared___boxed(
    mut v_00_u03b1_337_: *mut leanh::LeanObject,
    mut v_s_338_: *mut leanh::LeanObject,
    mut v_a_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_340_ = lean_dbg_trace_if_shared(v_s_338_, v_a_339_);
    return v_res_340_;
}
pub unsafe fn l_dbgStackTrace___boxed(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_f_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = lean_dbg_stack_trace(v_f_344_);
    return v_res_345_;
}
pub unsafe fn l_dbgStackTraceIf___redArg(
    mut v_cond_346_: u8,
    mut v_f_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_cond_346_ == 0 {
        let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_348_ = leanh::lean_box(0);
        v___x_349_ = leanh::lean_apply_1(v_f_347_, v___x_348_);
        return v___x_349_;
    } else {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = lean_dbg_stack_trace(v_f_347_);
        return v___x_350_;
    }
}
pub unsafe fn l_dbgStackTraceIf___redArg___boxed(
    mut v_cond_351_: *mut leanh::LeanObject,
    mut v_f_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cond_boxed_353_: u8 = 0;
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_353_ = (leanh::lean_unbox(v_cond_351_) as u8);
    v_res_354_ = l_dbgStackTraceIf___redArg(v_cond_boxed_353_, v_f_352_);
    return v_res_354_;
}
pub unsafe fn l_dbgStackTraceIf(
    mut v_00_u03b1_355_: *mut leanh::LeanObject,
    mut v_cond_356_: u8,
    mut v_f_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = l_dbgStackTraceIf___redArg(v_cond_356_, v_f_357_);
    return v___x_358_;
}
pub unsafe fn l_dbgStackTraceIf___boxed(
    mut v_00_u03b1_359_: *mut leanh::LeanObject,
    mut v_cond_360_: *mut leanh::LeanObject,
    mut v_f_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cond_boxed_362_: u8 = 0;
    let mut v_res_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_362_ = (leanh::lean_unbox(v_cond_360_) as u8);
    v_res_363_ = l_dbgStackTraceIf(v_00_u03b1_359_, v_cond_boxed_362_, v_f_361_);
    return v_res_363_;
}
pub unsafe fn l_dbgSleep___boxed(
    mut v_00_u03b1_367_: *mut leanh::LeanObject,
    mut v_ms_368_: *mut leanh::LeanObject,
    mut v_f_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ms_boxed_370_: u32 = 0;
    let mut v_res_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ms_boxed_370_ = leanh::lean_unbox_uint32(v_ms_368_);
    leanh::lean_dec(v_ms_368_);
    v_res_371_ = lean_dbg_sleep(v_ms_boxed_370_, v_f_369_);
    return v_res_371_;
}
pub unsafe fn l_mkPanicMessage(
    mut v_modName_375_: *mut leanh::LeanObject,
    mut v_line_376_: *mut leanh::LeanObject,
    mut v_col_377_: *mut leanh::LeanObject,
    mut v_msg_378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = l_mkPanicMessage___closed__0;
    v___x_380_ = lean_string_append(v___x_379_, v_modName_375_);
    v___x_381_ = l_mkPanicMessage___closed__1;
    v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
    v___x_383_ = l_Nat_reprFast(v_line_376_);
    v___x_384_ = lean_string_append(v___x_382_, v___x_383_);
    leanh::lean_dec_ref(v___x_383_);
    v___x_385_ = lean_string_append(v___x_384_, v___x_381_);
    v___x_386_ = l_Nat_reprFast(v_col_377_);
    v___x_387_ = lean_string_append(v___x_385_, v___x_386_);
    leanh::lean_dec_ref(v___x_386_);
    v___x_388_ = l_mkPanicMessage___closed__2;
    v___x_389_ = lean_string_append(v___x_387_, v___x_388_);
    v___x_390_ = lean_string_append(v___x_389_, v_msg_378_);
    return v___x_390_;
}
pub unsafe fn l_mkPanicMessage___boxed(
    mut v_modName_391_: *mut leanh::LeanObject,
    mut v_line_392_: *mut leanh::LeanObject,
    mut v_col_393_: *mut leanh::LeanObject,
    mut v_msg_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_mkPanicMessage(v_modName_391_, v_line_392_, v_col_393_, v_msg_394_);
    leanh::lean_dec_ref(v_msg_394_);
    leanh::lean_dec_ref(v_modName_391_);
    return v_res_395_;
}
pub unsafe fn l_panicWithPos___redArg(
    mut v_inst_396_: *mut leanh::LeanObject,
    mut v_modName_397_: *mut leanh::LeanObject,
    mut v_line_398_: *mut leanh::LeanObject,
    mut v_col_399_: *mut leanh::LeanObject,
    mut v_msg_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l_mkPanicMessage(v_modName_397_, v_line_398_, v_col_399_, v_msg_400_);
    v___x_402_ = l_panic___redArg(v_inst_396_, v___x_401_);
    return v___x_402_;
}
pub unsafe fn l_panicWithPos___redArg___boxed(
    mut v_inst_403_: *mut leanh::LeanObject,
    mut v_modName_404_: *mut leanh::LeanObject,
    mut v_line_405_: *mut leanh::LeanObject,
    mut v_col_406_: *mut leanh::LeanObject,
    mut v_msg_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_408_ = l_panicWithPos___redArg(
        v_inst_403_,
        v_modName_404_,
        v_line_405_,
        v_col_406_,
        v_msg_407_,
    );
    leanh::lean_dec_ref(v_msg_407_);
    leanh::lean_dec_ref(v_modName_404_);
    leanh::lean_dec(v_inst_403_);
    return v_res_408_;
}
pub unsafe fn l_panicWithPos(
    mut v_00_u03b1_409_: *mut leanh::LeanObject,
    mut v_inst_410_: *mut leanh::LeanObject,
    mut v_modName_411_: *mut leanh::LeanObject,
    mut v_line_412_: *mut leanh::LeanObject,
    mut v_col_413_: *mut leanh::LeanObject,
    mut v_msg_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = l_mkPanicMessage(v_modName_411_, v_line_412_, v_col_413_, v_msg_414_);
    v___x_416_ = l_panic___redArg(v_inst_410_, v___x_415_);
    return v___x_416_;
}
pub unsafe fn l_panicWithPos___boxed(
    mut v_00_u03b1_417_: *mut leanh::LeanObject,
    mut v_inst_418_: *mut leanh::LeanObject,
    mut v_modName_419_: *mut leanh::LeanObject,
    mut v_line_420_: *mut leanh::LeanObject,
    mut v_col_421_: *mut leanh::LeanObject,
    mut v_msg_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_panicWithPos(
        v_00_u03b1_417_,
        v_inst_418_,
        v_modName_419_,
        v_line_420_,
        v_col_421_,
        v_msg_422_,
    );
    leanh::lean_dec_ref(v_msg_422_);
    leanh::lean_dec_ref(v_modName_419_);
    leanh::lean_dec(v_inst_418_);
    return v_res_423_;
}
pub unsafe fn l_mkPanicMessageWithDecl(
    mut v_modName_425_: *mut leanh::LeanObject,
    mut v_declName_426_: *mut leanh::LeanObject,
    mut v_line_427_: *mut leanh::LeanObject,
    mut v_col_428_: *mut leanh::LeanObject,
    mut v_msg_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_mkPanicMessage___closed__0;
    v___x_431_ = lean_string_append(v___x_430_, v_declName_426_);
    v___x_432_ = l_mkPanicMessageWithDecl___closed__0;
    v___x_433_ = lean_string_append(v___x_431_, v___x_432_);
    v___x_434_ = lean_string_append(v___x_433_, v_modName_425_);
    v___x_435_ = l_mkPanicMessage___closed__1;
    v___x_436_ = lean_string_append(v___x_434_, v___x_435_);
    v___x_437_ = l_Nat_reprFast(v_line_427_);
    v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
    leanh::lean_dec_ref(v___x_437_);
    v___x_439_ = lean_string_append(v___x_438_, v___x_435_);
    v___x_440_ = l_Nat_reprFast(v_col_428_);
    v___x_441_ = lean_string_append(v___x_439_, v___x_440_);
    leanh::lean_dec_ref(v___x_440_);
    v___x_442_ = l_mkPanicMessage___closed__2;
    v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
    v___x_444_ = lean_string_append(v___x_443_, v_msg_429_);
    return v___x_444_;
}
pub unsafe fn l_mkPanicMessageWithDecl___boxed(
    mut v_modName_445_: *mut leanh::LeanObject,
    mut v_declName_446_: *mut leanh::LeanObject,
    mut v_line_447_: *mut leanh::LeanObject,
    mut v_col_448_: *mut leanh::LeanObject,
    mut v_msg_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_mkPanicMessageWithDecl(
        v_modName_445_,
        v_declName_446_,
        v_line_447_,
        v_col_448_,
        v_msg_449_,
    );
    leanh::lean_dec_ref(v_msg_449_);
    leanh::lean_dec_ref(v_declName_446_);
    leanh::lean_dec_ref(v_modName_445_);
    return v_res_450_;
}
pub unsafe fn l_panicWithPosWithDecl___redArg(
    mut v_inst_451_: *mut leanh::LeanObject,
    mut v_modName_452_: *mut leanh::LeanObject,
    mut v_declName_453_: *mut leanh::LeanObject,
    mut v_line_454_: *mut leanh::LeanObject,
    mut v_col_455_: *mut leanh::LeanObject,
    mut v_msg_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_457_ = l_mkPanicMessageWithDecl(
        v_modName_452_,
        v_declName_453_,
        v_line_454_,
        v_col_455_,
        v_msg_456_,
    );
    v___x_458_ = l_panic___redArg(v_inst_451_, v___x_457_);
    return v___x_458_;
}
pub unsafe fn l_panicWithPosWithDecl___redArg___boxed(
    mut v_inst_459_: *mut leanh::LeanObject,
    mut v_modName_460_: *mut leanh::LeanObject,
    mut v_declName_461_: *mut leanh::LeanObject,
    mut v_line_462_: *mut leanh::LeanObject,
    mut v_col_463_: *mut leanh::LeanObject,
    mut v_msg_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_panicWithPosWithDecl___redArg(
        v_inst_459_,
        v_modName_460_,
        v_declName_461_,
        v_line_462_,
        v_col_463_,
        v_msg_464_,
    );
    leanh::lean_dec_ref(v_msg_464_);
    leanh::lean_dec_ref(v_declName_461_);
    leanh::lean_dec_ref(v_modName_460_);
    leanh::lean_dec(v_inst_459_);
    return v_res_465_;
}
pub unsafe fn l_panicWithPosWithDecl(
    mut v_00_u03b1_466_: *mut leanh::LeanObject,
    mut v_inst_467_: *mut leanh::LeanObject,
    mut v_modName_468_: *mut leanh::LeanObject,
    mut v_declName_469_: *mut leanh::LeanObject,
    mut v_line_470_: *mut leanh::LeanObject,
    mut v_col_471_: *mut leanh::LeanObject,
    mut v_msg_472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_473_ = l_mkPanicMessageWithDecl(
        v_modName_468_,
        v_declName_469_,
        v_line_470_,
        v_col_471_,
        v_msg_472_,
    );
    v___x_474_ = l_panic___redArg(v_inst_467_, v___x_473_);
    return v___x_474_;
}
pub unsafe fn l_panicWithPosWithDecl___boxed(
    mut v_00_u03b1_475_: *mut leanh::LeanObject,
    mut v_inst_476_: *mut leanh::LeanObject,
    mut v_modName_477_: *mut leanh::LeanObject,
    mut v_declName_478_: *mut leanh::LeanObject,
    mut v_line_479_: *mut leanh::LeanObject,
    mut v_col_480_: *mut leanh::LeanObject,
    mut v_msg_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_panicWithPosWithDecl(
        v_00_u03b1_475_,
        v_inst_476_,
        v_modName_477_,
        v_declName_478_,
        v_line_479_,
        v_col_480_,
        v_msg_481_,
    );
    leanh::lean_dec_ref(v_msg_481_);
    leanh::lean_dec_ref(v_declName_478_);
    leanh::lean_dec_ref(v_modName_477_);
    leanh::lean_dec(v_inst_476_);
    return v_res_482_;
}
pub unsafe fn l_ptrAddrUnsafe___boxed(
    mut v_00_u03b1_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_487_: usize = 0;
    let mut v_r_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_487_ = lean_ptr_addr(v_a_486_);
    leanh::lean_dec(v_a_486_);
    v_r_488_ = leanh::lean_box_usize(v_res_487_);
    return v_r_488_;
}
pub unsafe fn l_isExclusiveUnsafe___boxed(
    mut v_00_u03b1_491_: *mut leanh::LeanObject,
    mut v_a_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_493_: u8 = 0;
    let mut v_r_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = lean_is_exclusive_obj(v_a_492_);
    leanh::lean_dec(v_a_492_);
    v_r_494_ = leanh::lean_box((v_res_493_) as usize);
    return v_r_494_;
}
pub unsafe fn l_withPtrAddrUnsafe___redArg(
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_k_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_497_: usize = 0;
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_497_ = lean_ptr_addr(v_a_495_);
    v___x_498_ = leanh::lean_box_usize(v___x_497_);
    v___x_499_ = leanh::lean_apply_1(v_k_496_, v___x_498_);
    return v___x_499_;
}
pub unsafe fn l_withPtrAddrUnsafe___redArg___boxed(
    mut v_a_500_: *mut leanh::LeanObject,
    mut v_k_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_withPtrAddrUnsafe___redArg(v_a_500_, v_k_501_);
    leanh::lean_dec(v_a_500_);
    return v_res_502_;
}
pub unsafe fn l_withPtrAddrUnsafe(
    mut v_00_u03b1_503_: *mut leanh::LeanObject,
    mut v_00_u03b2_504_: *mut leanh::LeanObject,
    mut v_a_505_: *mut leanh::LeanObject,
    mut v_k_506_: *mut leanh::LeanObject,
    mut v_h_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_508_: usize = 0;
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_508_ = lean_ptr_addr(v_a_505_);
    v___x_509_ = leanh::lean_box_usize(v___x_508_);
    v___x_510_ = leanh::lean_apply_1(v_k_506_, v___x_509_);
    return v___x_510_;
}
pub unsafe fn l_withPtrAddrUnsafe___boxed(
    mut v_00_u03b1_511_: *mut leanh::LeanObject,
    mut v_00_u03b2_512_: *mut leanh::LeanObject,
    mut v_a_513_: *mut leanh::LeanObject,
    mut v_k_514_: *mut leanh::LeanObject,
    mut v_h_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_withPtrAddrUnsafe(
        v_00_u03b1_511_,
        v_00_u03b2_512_,
        v_a_513_,
        v_k_514_,
        v_h_515_,
    );
    leanh::lean_dec(v_a_513_);
    return v_res_516_;
}
pub unsafe fn l_ptrEq___redArg(
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_b_518_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_519_: usize = 0;
    let mut v___x_520_: usize = 0;
    let mut v___x_521_: u8 = 0;
    v___x_519_ = lean_ptr_addr(v_a_517_);
    v___x_520_ = lean_ptr_addr(v_b_518_);
    v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
    return v___x_521_;
}
pub unsafe fn l_ptrEq___redArg___boxed(
    mut v_a_522_: *mut leanh::LeanObject,
    mut v_b_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: u8 = 0;
    let mut v_r_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_ptrEq___redArg(v_a_522_, v_b_523_);
    leanh::lean_dec(v_b_523_);
    leanh::lean_dec(v_a_522_);
    v_r_525_ = leanh::lean_box((v_res_524_) as usize);
    return v_r_525_;
}
pub unsafe fn l_ptrEq(
    mut v_00_u03b1_526_: *mut leanh::LeanObject,
    mut v_a_527_: *mut leanh::LeanObject,
    mut v_b_528_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_529_: usize = 0;
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: u8 = 0;
    v___x_529_ = lean_ptr_addr(v_a_527_);
    v___x_530_ = lean_ptr_addr(v_b_528_);
    v___x_531_ = lean_usize_dec_eq(v___x_529_, v___x_530_);
    return v___x_531_;
}
pub unsafe fn l_ptrEq___boxed(
    mut v_00_u03b1_532_: *mut leanh::LeanObject,
    mut v_a_533_: *mut leanh::LeanObject,
    mut v_b_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_535_: u8 = 0;
    let mut v_r_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_ptrEq(v_00_u03b1_532_, v_a_533_, v_b_534_);
    leanh::lean_dec(v_b_534_);
    leanh::lean_dec(v_a_533_);
    v_r_536_ = leanh::lean_box((v_res_535_) as usize);
    return v_r_536_;
}
pub unsafe fn l_ptrEqList___redArg(
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_x_538_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: u8 = 0;
    let mut v_head_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: usize = 0;
    let mut v___x_546_: usize = 0;
    let mut v___x_547_: u8 = 0;
    let mut v___x_549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_537_) == 0 {
                    if leanh::lean_obj_tag(v_x_538_) == 0 {
                        v___x_539_ = 1;
                        return v___x_539_;
                    } else {
                        v___x_540_ = 0;
                        return v___x_540_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_538_) == 1 {
                        v_head_541_ = leanh::lean_ctor_get(v_x_537_, 0);
                        v_tail_542_ = leanh::lean_ctor_get(v_x_537_, 1);
                        v_head_543_ = leanh::lean_ctor_get(v_x_538_, 0);
                        v_tail_544_ = leanh::lean_ctor_get(v_x_538_, 1);
                        v___x_545_ = lean_ptr_addr(v_head_541_);
                        v___x_546_ = lean_ptr_addr(v_head_543_);
                        v___x_547_ = lean_usize_dec_eq(v___x_545_, v___x_546_);
                        if v___x_547_ == 0 {
                            return v___x_547_;
                        } else {
                            v_x_537_ = v_tail_542_;
                            v_x_538_ = v_tail_544_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_549_ = 0;
                        return v___x_549_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ptrEqList___redArg___boxed(
    mut v_x_550_: *mut leanh::LeanObject,
    mut v_x_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_552_: u8 = 0;
    let mut v_r_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_552_ = l_ptrEqList___redArg(v_x_550_, v_x_551_);
    leanh::lean_dec(v_x_551_);
    leanh::lean_dec(v_x_550_);
    v_r_553_ = leanh::lean_box((v_res_552_) as usize);
    return v_r_553_;
}
pub unsafe fn l_ptrEqList(
    mut v_00_u03b1_554_: *mut leanh::LeanObject,
    mut v_x_555_: *mut leanh::LeanObject,
    mut v_x_556_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_557_: u8 = 0;
    v___x_557_ = l_ptrEqList___redArg(v_x_555_, v_x_556_);
    return v___x_557_;
}
pub unsafe fn l_ptrEqList___boxed(
    mut v_00_u03b1_558_: *mut leanh::LeanObject,
    mut v_x_559_: *mut leanh::LeanObject,
    mut v_x_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_561_: u8 = 0;
    let mut v_r_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_561_ = l_ptrEqList(v_00_u03b1_558_, v_x_559_, v_x_560_);
    leanh::lean_dec(v_x_560_);
    leanh::lean_dec(v_x_559_);
    v_r_562_ = leanh::lean_box((v_res_561_) as usize);
    return v_r_562_;
}
pub unsafe fn l_withPtrEqUnsafe___redArg(
    mut v_a_563_: *mut leanh::LeanObject,
    mut v_b_564_: *mut leanh::LeanObject,
    mut v_k_565_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_566_: usize = 0;
    let mut v___x_567_: usize = 0;
    let mut v___x_568_: u8 = 0;
    v___x_566_ = lean_ptr_addr(v_a_563_);
    v___x_567_ = lean_ptr_addr(v_b_564_);
    v___x_568_ = lean_usize_dec_eq(v___x_566_, v___x_567_);
    if v___x_568_ == 0 {
        let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_571_: u8 = 0;
        v___x_569_ = leanh::lean_box(0);
        v___x_570_ = leanh::lean_apply_1(v_k_565_, v___x_569_);
        v___x_571_ = (leanh::lean_unbox(v___x_570_) as u8);
        return v___x_571_;
    } else {
        leanh::lean_dec_ref(v_k_565_);
        return v___x_568_;
    }
}
pub unsafe fn l_withPtrEqUnsafe___redArg___boxed(
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_b_573_: *mut leanh::LeanObject,
    mut v_k_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_575_: u8 = 0;
    let mut v_r_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_withPtrEqUnsafe___redArg(v_a_572_, v_b_573_, v_k_574_);
    leanh::lean_dec(v_b_573_);
    leanh::lean_dec(v_a_572_);
    v_r_576_ = leanh::lean_box((v_res_575_) as usize);
    return v_r_576_;
}
pub unsafe fn l_withPtrEqUnsafe(
    mut v_00_u03b1_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
    mut v_b_579_: *mut leanh::LeanObject,
    mut v_k_580_: *mut leanh::LeanObject,
    mut v_h_581_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_582_: usize = 0;
    let mut v___x_583_: usize = 0;
    let mut v___x_584_: u8 = 0;
    v___x_582_ = lean_ptr_addr(v_a_578_);
    v___x_583_ = lean_ptr_addr(v_b_579_);
    v___x_584_ = lean_usize_dec_eq(v___x_582_, v___x_583_);
    if v___x_584_ == 0 {
        let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_587_: u8 = 0;
        v___x_585_ = leanh::lean_box(0);
        v___x_586_ = leanh::lean_apply_1(v_k_580_, v___x_585_);
        v___x_587_ = (leanh::lean_unbox(v___x_586_) as u8);
        return v___x_587_;
    } else {
        leanh::lean_dec_ref(v_k_580_);
        return v___x_584_;
    }
}
pub unsafe fn l_withPtrEqUnsafe___boxed(
    mut v_00_u03b1_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
    mut v_b_590_: *mut leanh::LeanObject,
    mut v_k_591_: *mut leanh::LeanObject,
    mut v_h_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_593_: u8 = 0;
    let mut v_r_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_593_ = l_withPtrEqUnsafe(v_00_u03b1_588_, v_a_589_, v_b_590_, v_k_591_, v_h_592_);
    leanh::lean_dec(v_b_590_);
    leanh::lean_dec(v_a_589_);
    v_r_594_ = leanh::lean_box((v_res_593_) as usize);
    return v_r_594_;
}
pub unsafe fn l_withPtrEqDecEq___redArg(
    mut v_a_595_: *mut leanh::LeanObject,
    mut v_b_596_: *mut leanh::LeanObject,
    mut v_k_597_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_598_: usize = 0;
    let mut v___x_599_: usize = 0;
    let mut v___x_600_: u8 = 0;
    v___x_598_ = lean_ptr_addr(v_a_595_);
    v___x_599_ = lean_ptr_addr(v_b_596_);
    v___x_600_ = lean_usize_dec_eq(v___x_598_, v___x_599_);
    if v___x_600_ == 0 {
        let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_603_: u8 = 0;
        v___x_601_ = leanh::lean_box(0);
        v___x_602_ = leanh::lean_apply_1(v_k_597_, v___x_601_);
        v___x_603_ = (leanh::lean_unbox(v___x_602_) as u8);
        return v___x_603_;
    } else {
        leanh::lean_dec_ref(v_k_597_);
        return v___x_600_;
    }
}
pub unsafe fn l_withPtrEqDecEq___redArg___boxed(
    mut v_a_604_: *mut leanh::LeanObject,
    mut v_b_605_: *mut leanh::LeanObject,
    mut v_k_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_607_: u8 = 0;
    let mut v_r_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_607_ = l_withPtrEqDecEq___redArg(v_a_604_, v_b_605_, v_k_606_);
    leanh::lean_dec(v_b_605_);
    leanh::lean_dec(v_a_604_);
    v_r_608_ = leanh::lean_box((v_res_607_) as usize);
    return v_r_608_;
}
pub unsafe fn l_withPtrEqDecEq(
    mut v_00_u03b1_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_b_611_: *mut leanh::LeanObject,
    mut v_k_612_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_613_: usize = 0;
    let mut v___x_614_: usize = 0;
    let mut v___x_615_: u8 = 0;
    v___x_613_ = lean_ptr_addr(v_a_610_);
    v___x_614_ = lean_ptr_addr(v_b_611_);
    v___x_615_ = lean_usize_dec_eq(v___x_613_, v___x_614_);
    if v___x_615_ == 0 {
        let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_618_: u8 = 0;
        v___x_616_ = leanh::lean_box(0);
        v___x_617_ = leanh::lean_apply_1(v_k_612_, v___x_616_);
        v___x_618_ = (leanh::lean_unbox(v___x_617_) as u8);
        return v___x_618_;
    } else {
        leanh::lean_dec_ref(v_k_612_);
        return v___x_615_;
    }
}
pub unsafe fn l_withPtrEqDecEq___boxed(
    mut v_00_u03b1_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
    mut v_b_621_: *mut leanh::LeanObject,
    mut v_k_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_623_: u8 = 0;
    let mut v_r_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_623_ = l_withPtrEqDecEq(v_00_u03b1_619_, v_a_620_, v_b_621_, v_k_622_);
    leanh::lean_dec(v_b_621_);
    leanh::lean_dec(v_a_620_);
    v_r_624_ = leanh::lean_box((v_res_623_) as usize);
    return v_r_624_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Util(builtin);
}