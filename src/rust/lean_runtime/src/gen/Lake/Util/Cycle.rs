// Lean compiler output
// Module: Lake.Util.Cycle
// Imports: Init.Data.ToString
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map,
    l_ExceptT_pure,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_elem___redArg, l_List_mapTR_loop___redArg,
    l_List_partition_loop___redArg,
};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Prelude::l_ReaderT_read___boxed;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_unbox,
};
pub static l_Lake_formatCycle___redArg___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [32, 32, 0],
    };
static mut l_Lake_formatCycle___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_formatCycle___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_formatCycle___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l_Lake_formatCycle___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_formatCycle___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0_value:
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
    m_fun: l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_guardCycle___redArg___lam__1___closed__0_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_guardCycle___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_guardCycle___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_formatCycle___redArg___lam__0(
    mut v_inst_248_: *mut LeanObject,
    mut v_x_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v___x_250_ = l_Lake_formatCycle___redArg___lam__0___closed__0;
    v___x_251_ = lean_apply_1(v_inst_248_, v_x_249_);
    v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
    lean_dec_ref(v___x_251_);
    return v___x_252_;
}
pub unsafe fn l_Lake_formatCycle___redArg(
    mut v_inst_254_: *mut LeanObject,
    mut v_cycle_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___f_256_ = lean_alloc_closure(
        l_Lake_formatCycle___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_256_, 0, v_inst_254_);
    v___x_257_ = l_Lake_formatCycle___redArg___closed__0;
    v___x_258_ = lean_box(0);
    v___x_259_ = l_List_mapTR_loop___redArg(v___f_256_, v_cycle_255_, v___x_258_);
    v___x_260_ = l_String_intercalate(v___x_257_, v___x_259_);
    return v___x_260_;
}
pub unsafe fn l_Lake_formatCycle(
    mut v_00_u03ba_261_: *mut LeanObject,
    mut v_inst_262_: *mut LeanObject,
    mut v_cycle_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Lake_formatCycle___redArg(v_inst_262_, v_cycle_263_);
    return v___x_264_;
}
pub unsafe fn l_Lake_instMonadCallStackOfMonadCallStackOf___redArg___lam__0(
    mut v_withCallStack_265_: *mut LeanObject,
    mut v_00_u03b1_266_: *mut LeanObject,
    mut v___y_267_: *mut LeanObject,
    mut v___y_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    v___x_269_ = lean_apply_3(v_withCallStack_265_, lean_box(0), v___y_267_, v___y_268_);
    return v___x_269_;
}
pub unsafe fn l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(
    mut v_inst_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCallStack_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_275_: u8 = 0;
    let mut v___f_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCallStack_271_ = lean_ctor_get(v_inst_270_, 0);
                v_withCallStack_272_ = lean_ctor_get(v_inst_270_, 1);
                v_isSharedCheck_280_ = (!lean_is_exclusive(v_inst_270_)) as u8;
                if v_isSharedCheck_280_ == 0 {
                    v___x_274_ = v_inst_270_;
                    v_isShared_275_ = v_isSharedCheck_280_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_withCallStack_272_);
                    lean_inc(v_getCallStack_271_);
                    lean_dec(v_inst_270_);
                    v___x_274_ = lean_box(0);
                    v_isShared_275_ = v_isSharedCheck_280_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_276_ = lean_alloc_closure(
                    l_Lake_instMonadCallStackOfMonadCallStackOf___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_276_, 0, v_withCallStack_272_);
                if v_isShared_275_ == 0 {
                    lean_ctor_set(v___x_274_, 1, v___f_276_);
                    v___x_278_ = v___x_274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_279_, 0, v_getCallStack_271_);
                    lean_ctor_set(v_reuseFailAlloc_279_, 1, v___f_276_);
                    v___x_278_ = v_reuseFailAlloc_279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadCallStackOfMonadCallStackOf(
    mut v_00_u03ba_281_: *mut LeanObject,
    mut v_m_282_: *mut LeanObject,
    mut v_inst_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    v___x_284_ = l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(v_inst_283_);
    return v___x_284_;
}
pub unsafe fn l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__0(
    mut v_withCallStack_285_: *mut LeanObject,
    mut v_s_286_: *mut LeanObject,
    mut v_00_u03b2_287_: *mut LeanObject,
    mut v___y_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    v___x_289_ = lean_apply_3(v_withCallStack_285_, lean_box(0), v_s_286_, v___y_288_);
    return v___x_289_;
}
pub unsafe fn l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__1(
    mut v_withCallStack_290_: *mut LeanObject,
    mut v_inst_291_: *mut LeanObject,
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_s_293_: *mut LeanObject,
    mut v___y_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    v___f_295_ = lean_alloc_closure(
        l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_295_, 0, v_withCallStack_290_);
    lean_closure_set(v___f_295_, 1, v_s_293_);
    v___x_296_ = lean_apply_3(v_inst_291_, lean_box(0), v___f_295_, v___y_294_);
    return v___x_296_;
}
pub unsafe fn l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
    mut v_inst_297_: *mut LeanObject,
    mut v_inst_298_: *mut LeanObject,
    mut v_inst_299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_getCallStack_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_304_: u8 = 0;
    let mut v___f_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getCallStack_300_ = lean_ctor_get(v_inst_299_, 0);
                v_withCallStack_301_ = lean_ctor_get(v_inst_299_, 1);
                v_isSharedCheck_310_ = (!lean_is_exclusive(v_inst_299_)) as u8;
                if v_isSharedCheck_310_ == 0 {
                    v___x_303_ = v_inst_299_;
                    v_isShared_304_ = v_isSharedCheck_310_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_withCallStack_301_);
                    lean_inc(v_getCallStack_300_);
                    lean_dec(v_inst_299_);
                    v___x_303_ = lean_box(0);
                    v_isShared_304_ = v_isSharedCheck_310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_305_ = lean_alloc_closure(
                    l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg___lam__1
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_305_, 0, v_withCallStack_301_);
                lean_closure_set(v___f_305_, 1, v_inst_298_);
                v___x_306_ = lean_apply_2(v_inst_297_, lean_box(0), v_getCallStack_300_);
                if v_isShared_304_ == 0 {
                    lean_ctor_set(v___x_303_, 1, v___f_305_);
                    lean_ctor_set(v___x_303_, 0, v___x_306_);
                    v___x_308_ = v___x_303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
                    lean_ctor_set(v_reuseFailAlloc_309_, 1, v___f_305_);
                    v___x_308_ = v_reuseFailAlloc_309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor(
    mut v_m_311_: *mut LeanObject,
    mut v_n_312_: *mut LeanObject,
    mut v_00_u03ba_313_: *mut LeanObject,
    mut v_inst_314_: *mut LeanObject,
    mut v_inst_315_: *mut LeanObject,
    mut v_inst_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
        v_inst_314_,
        v_inst_315_,
        v_inst_316_,
    );
    return v___x_317_;
}
pub unsafe fn l_Lake_instMonadCycleOfMonadCycleOf___redArg___lam__0(
    mut v_throwCycle_318_: *mut LeanObject,
    mut v_00_u03b1_319_: *mut LeanObject,
    mut v___y_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = lean_apply_2(v_throwCycle_318_, lean_box(0), v___y_320_);
    return v___x_321_;
}
pub unsafe fn l_Lake_instMonadCycleOfMonadCycleOf___redArg(
    mut v_inst_322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadCallStackOf_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v___f_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadCallStackOf_323_ = lean_ctor_get(v_inst_322_, 0);
                v_throwCycle_324_ = lean_ctor_get(v_inst_322_, 1);
                v_isSharedCheck_333_ = (!lean_is_exclusive(v_inst_322_)) as u8;
                if v_isSharedCheck_333_ == 0 {
                    v___x_326_ = v_inst_322_;
                    v_isShared_327_ = v_isSharedCheck_333_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_throwCycle_324_);
                    lean_inc(v_toMonadCallStackOf_323_);
                    lean_dec(v_inst_322_);
                    v___x_326_ = lean_box(0);
                    v_isShared_327_ = v_isSharedCheck_333_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_328_ = lean_alloc_closure(
                    l_Lake_instMonadCycleOfMonadCycleOf___redArg___lam__0 as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_328_, 0, v_throwCycle_324_);
                v___x_329_ =
                    l_Lake_instMonadCallStackOfMonadCallStackOf___redArg(v_toMonadCallStackOf_323_);
                if v_isShared_327_ == 0 {
                    lean_ctor_set(v___x_326_, 1, v___f_328_);
                    lean_ctor_set(v___x_326_, 0, v___x_329_);
                    v___x_331_ = v___x_326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
                    lean_ctor_set(v_reuseFailAlloc_332_, 1, v___f_328_);
                    v___x_331_ = v_reuseFailAlloc_332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadCycleOfMonadCycleOf(
    mut v_00_u03ba_334_: *mut LeanObject,
    mut v_m_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = l_Lake_instMonadCycleOfMonadCycleOf___redArg(v_inst_336_);
    return v___x_337_;
}
pub unsafe fn l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg___lam__0(
    mut v_throwCycle_338_: *mut LeanObject,
    mut v_inst_339_: *mut LeanObject,
    mut v_00_u03b1_340_: *mut LeanObject,
    mut v_cycle_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_apply_2(v_throwCycle_338_, lean_box(0), v_cycle_341_);
    v___x_343_ = lean_apply_2(v_inst_339_, lean_box(0), v___x_342_);
    return v___x_343_;
}
pub unsafe fn l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg(
    mut v_inst_344_: *mut LeanObject,
    mut v_inst_345_: *mut LeanObject,
    mut v_inst_346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadCallStackOf_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_351_: u8 = 0;
    let mut v___f_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toMonadCallStackOf_347_ = lean_ctor_get(v_inst_346_, 0);
                v_throwCycle_348_ = lean_ctor_get(v_inst_346_, 1);
                v_isSharedCheck_357_ = (!lean_is_exclusive(v_inst_346_)) as u8;
                if v_isSharedCheck_357_ == 0 {
                    v___x_350_ = v_inst_346_;
                    v_isShared_351_ = v_isSharedCheck_357_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_throwCycle_348_);
                    lean_inc(v_toMonadCallStackOf_347_);
                    lean_dec(v_inst_346_);
                    v___x_350_ = lean_box(0);
                    v_isShared_351_ = v_isSharedCheck_357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_inst_344_);
                v___f_352_ = lean_alloc_closure(
                    l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg___lam__0
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_352_, 0, v_throwCycle_348_);
                lean_closure_set(v___f_352_, 1, v_inst_344_);
                v___x_353_ = l_Lake_instMonadCallStackOfOfMonadLiftOfMonadFunctor___redArg(
                    v_inst_344_,
                    v_inst_345_,
                    v_toMonadCallStackOf_347_,
                );
                if v_isShared_351_ == 0 {
                    lean_ctor_set(v___x_350_, 1, v___f_352_);
                    lean_ctor_set(v___x_350_, 0, v___x_353_);
                    v___x_355_ = v___x_350_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
                    lean_ctor_set(v_reuseFailAlloc_356_, 1, v___f_352_);
                    v___x_355_ = v_reuseFailAlloc_356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor(
    mut v_m_358_: *mut LeanObject,
    mut v_n_359_: *mut LeanObject,
    mut v_00_u03ba_360_: *mut LeanObject,
    mut v_inst_361_: *mut LeanObject,
    mut v_inst_362_: *mut LeanObject,
    mut v_inst_363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v___x_364_ = l_Lake_instMonadCycleOfOfMonadLiftOfMonadFunctor___redArg(
        v_inst_361_,
        v_inst_362_,
        v_inst_363_,
    );
    return v___x_364_;
}
pub unsafe fn l_Lake_inhabitedOfMonadCycle___redArg(
    mut v_inst_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throwCycle_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v_throwCycle_366_ = lean_ctor_get(v_inst_365_, 1);
    lean_inc(v_throwCycle_366_);
    lean_dec_ref(v_inst_365_);
    v___x_367_ = lean_box(0);
    v___x_368_ = lean_apply_2(v_throwCycle_366_, lean_box(0), v___x_367_);
    return v___x_368_;
}
pub unsafe fn l_Lake_inhabitedOfMonadCycle(
    mut v_00_u03ba_369_: *mut LeanObject,
    mut v_m_370_: *mut LeanObject,
    mut v_00_u03b1_371_: *mut LeanObject,
    mut v_inst_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = l_Lake_inhabitedOfMonadCycle___redArg(v_inst_372_);
    return v___x_373_;
}
pub unsafe fn l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0(
    mut v_00_u03b1_374_: *mut LeanObject,
    mut v_s_375_: *mut LeanObject,
    mut v_x_376_: *mut LeanObject,
    mut v___y_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    v___x_378_ = lean_apply_1(v_x_376_, v_s_375_);
    return v___x_378_;
}
pub unsafe fn l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0___boxed(
    mut v_00_u03b1_379_: *mut LeanObject,
    mut v_s_380_: *mut LeanObject,
    mut v_x_381_: *mut LeanObject,
    mut v___y_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_383_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___lam__0(
        v_00_u03b1_379_,
        v_s_380_,
        v_x_381_,
        v___y_382_,
    );
    lean_dec(v___y_382_);
    return v_res_383_;
}
pub unsafe fn l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(
    mut v_inst_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    v___f_386_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg___closed__0;
    v___x_387_ = lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_387_, 0, lean_box(0));
    lean_closure_set(v___x_387_, 1, lean_box(0));
    lean_closure_set(v___x_387_, 2, v_inst_385_);
    v___x_388_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_388_, 0, v___x_387_);
    lean_ctor_set(v___x_388_, 1, v___f_386_);
    return v___x_388_;
}
pub unsafe fn l_Lake_instMonadCallStackOfCallStackTOfMonad(
    mut v_m_389_: *mut LeanObject,
    mut v_00_u03ba_390_: *mut LeanObject,
    mut v_inst_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v_inst_391_);
    return v___x_392_;
}
pub unsafe fn l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0(
    mut v_inst_393_: *mut LeanObject,
    mut v_00_u03b1_394_: *mut LeanObject,
    mut v___y_395_: *mut LeanObject,
    mut v___y_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_397_ = lean_ctor_get(v_inst_393_, 0);
    lean_inc_ref(v_toApplicative_397_);
    lean_dec_ref(v_inst_393_);
    v_toPure_398_ = lean_ctor_get(v_toApplicative_397_, 1);
    lean_inc(v_toPure_398_);
    lean_dec_ref(v_toApplicative_397_);
    v___x_399_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_399_, 0, v___y_395_);
    v___x_400_ = lean_apply_2(v_toPure_398_, lean_box(0), v___x_399_);
    return v___x_400_;
}
pub unsafe fn l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0___boxed(
    mut v_inst_401_: *mut LeanObject,
    mut v_00_u03b1_402_: *mut LeanObject,
    mut v___y_403_: *mut LeanObject,
    mut v___y_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_405_: *mut LeanObject = core::ptr::null_mut();
    v_res_405_ = l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0(
        v_inst_401_,
        v_00_u03b1_402_,
        v___y_403_,
        v___y_404_,
    );
    lean_dec(v___y_404_);
    return v_res_405_;
}
pub unsafe fn l_Lake_instMonadCycleOfCycleTOfMonad___redArg(
    mut v_inst_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_406_, 7);
    v___f_407_ = lean_alloc_closure(
        l_Lake_instMonadCycleOfCycleTOfMonad___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_407_, 0, v_inst_406_);
    v___f_408_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_408_, 0, v_inst_406_);
    v___f_409_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_409_, 0, v_inst_406_);
    v___f_410_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_410_, 0, v_inst_406_);
    v___f_411_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_411_, 0, v_inst_406_);
    v___x_412_ = lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_412_, 0, lean_box(0));
    lean_closure_set(v___x_412_, 1, lean_box(0));
    lean_closure_set(v___x_412_, 2, v_inst_406_);
    v___x_413_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_413_, 0, v___x_412_);
    lean_ctor_set(v___x_413_, 1, v___f_408_);
    v___x_414_ = lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_414_, 0, lean_box(0));
    lean_closure_set(v___x_414_, 1, lean_box(0));
    lean_closure_set(v___x_414_, 2, v_inst_406_);
    v___x_415_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_415_, 0, v___x_413_);
    lean_ctor_set(v___x_415_, 1, v___x_414_);
    lean_ctor_set(v___x_415_, 2, v___f_409_);
    lean_ctor_set(v___x_415_, 3, v___f_410_);
    lean_ctor_set(v___x_415_, 4, v___f_411_);
    v___x_416_ = lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_416_, 0, lean_box(0));
    lean_closure_set(v___x_416_, 1, lean_box(0));
    lean_closure_set(v___x_416_, 2, v_inst_406_);
    v___x_417_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_417_, 0, v___x_415_);
    lean_ctor_set(v___x_417_, 1, v___x_416_);
    v___x_418_ = l_Lake_instMonadCallStackOfCallStackTOfMonad___redArg(v___x_417_);
    v___x_419_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_419_, 0, v___x_418_);
    lean_ctor_set(v___x_419_, 1, v___f_407_);
    return v___x_419_;
}
pub unsafe fn l_Lake_instMonadCycleOfCycleTOfMonad(
    mut v_m_420_: *mut LeanObject,
    mut v_00_u03ba_421_: *mut LeanObject,
    mut v_inst_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = l_Lake_instMonadCycleOfCycleTOfMonad___redArg(v_inst_422_);
    return v___x_423_;
}
pub unsafe fn l_Lake_guardCycle___redArg___lam__0(
    mut v_inst_424_: *mut LeanObject,
    mut v_key_425_: *mut LeanObject,
    mut v___x_426_: u8,
    mut v_x_427_: *mut LeanObject,
) -> u8 {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: u8 = 0;
    v___x_428_ = lean_apply_2(v_inst_424_, v_x_427_, v_key_425_);
    v___x_429_ = (lean_unbox(v___x_428_) as u8);
    if v___x_429_ == 0 {
        return v___x_426_;
    } else {
        let mut v___x_430_: u8 = 0;
        v___x_430_ = 0;
        return v___x_430_;
    }
}
pub unsafe fn l_Lake_guardCycle___redArg___lam__0___boxed(
    mut v_inst_431_: *mut LeanObject,
    mut v_key_432_: *mut LeanObject,
    mut v___x_433_: *mut LeanObject,
    mut v_x_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_153__boxed_435_: u8 = 0;
    let mut v_res_436_: u8 = 0;
    let mut v_r_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_153__boxed_435_ = (lean_unbox(v___x_433_) as u8);
    v_res_436_ = l_Lake_guardCycle___redArg___lam__0(
        v_inst_431_,
        v_key_432_,
        v___x_153__boxed_435_,
        v_x_434_,
    );
    v_r_437_ = lean_box((v_res_436_) as usize);
    return v_r_437_;
}
pub unsafe fn l_Lake_guardCycle___redArg___lam__1(
    mut v_inst_440_: *mut LeanObject,
    mut v_key_441_: *mut LeanObject,
    mut v_withCallStack_442_: *mut LeanObject,
    mut v_act_443_: *mut LeanObject,
    mut v_throwCycle_444_: *mut LeanObject,
    mut v_parents_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: u8 = 0;
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v_unused_465_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_parents_445_);
                lean_inc(v_key_441_);
                lean_inc_ref(v_inst_440_);
                v___x_446_ = l_List_elem___redArg(v_inst_440_, v_key_441_, v_parents_445_);
                if v___x_446_ == 0 {
                    lean_dec(v_throwCycle_444_);
                    lean_dec_ref(v_inst_440_);
                    v___x_447_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_447_, 0, v_key_441_);
                    lean_ctor_set(v___x_447_, 1, v_parents_445_);
                    v___x_448_ =
                        lean_apply_3(v_withCallStack_442_, lean_box(0), v___x_447_, v_act_443_);
                    return v___x_448_;
                } else {
                    lean_dec(v_act_443_);
                    lean_dec(v_withCallStack_442_);
                    v___x_449_ = lean_box((v___x_446_) as usize);
                    lean_inc(v_key_441_);
                    v___f_450_ = lean_alloc_closure(
                        l_Lake_guardCycle___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_450_, 0, v_inst_440_);
                    lean_closure_set(v___f_450_, 1, v_key_441_);
                    lean_closure_set(v___f_450_, 2, v___x_449_);
                    v___x_451_ = lean_box(0);
                    v___x_452_ = l_Lake_guardCycle___redArg___lam__1___closed__0;
                    v___x_453_ =
                        l_List_partition_loop___redArg(v___f_450_, v_parents_445_, v___x_452_);
                    v_fst_454_ = lean_ctor_get(v___x_453_, 0);
                    v_isSharedCheck_464_ = (!lean_is_exclusive(v___x_453_)) as u8;
                    if v_isSharedCheck_464_ == 0 {
                        v_unused_465_ = lean_ctor_get(v___x_453_, 1);
                        lean_dec(v_unused_465_);
                        v___x_456_ = v___x_453_;
                        v_isShared_457_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_454_);
                        lean_dec(v___x_453_);
                        v___x_456_ = lean_box(0);
                        v_isShared_457_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_key_441_);
                if v_isShared_457_ == 0 {
                    lean_ctor_set_tag(v___x_456_, 1);
                    lean_ctor_set(v___x_456_, 1, v_fst_454_);
                    lean_ctor_set(v___x_456_, 0, v_key_441_);
                    v___x_459_ = v___x_456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_463_, 0, v_key_441_);
                    lean_ctor_set(v_reuseFailAlloc_463_, 1, v_fst_454_);
                    v___x_459_ = v_reuseFailAlloc_463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_460_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_460_, 0, v_key_441_);
                lean_ctor_set(v___x_460_, 1, v___x_451_);
                v___x_461_ = l_List_appendTR___redArg(v___x_459_, v___x_460_);
                v___x_462_ = lean_apply_2(v_throwCycle_444_, lean_box(0), v___x_461_);
                return v___x_462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_guardCycle___redArg(
    mut v_inst_466_: *mut LeanObject,
    mut v_inst_467_: *mut LeanObject,
    mut v_inst_468_: *mut LeanObject,
    mut v_key_469_: *mut LeanObject,
    mut v_act_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadCallStack_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCallStack_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadCallStack_471_ = lean_ctor_get(v_inst_468_, 0);
    lean_inc_ref(v_toMonadCallStack_471_);
    v_toBind_472_ = lean_ctor_get(v_inst_467_, 1);
    lean_inc(v_toBind_472_);
    lean_dec_ref(v_inst_467_);
    v_throwCycle_473_ = lean_ctor_get(v_inst_468_, 1);
    lean_inc(v_throwCycle_473_);
    lean_dec_ref(v_inst_468_);
    v_getCallStack_474_ = lean_ctor_get(v_toMonadCallStack_471_, 0);
    lean_inc(v_getCallStack_474_);
    v_withCallStack_475_ = lean_ctor_get(v_toMonadCallStack_471_, 1);
    lean_inc(v_withCallStack_475_);
    lean_dec_ref(v_toMonadCallStack_471_);
    v___f_476_ = lean_alloc_closure(
        l_Lake_guardCycle___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_476_, 0, v_inst_466_);
    lean_closure_set(v___f_476_, 1, v_key_469_);
    lean_closure_set(v___f_476_, 2, v_withCallStack_475_);
    lean_closure_set(v___f_476_, 3, v_act_470_);
    lean_closure_set(v___f_476_, 4, v_throwCycle_473_);
    v___x_477_ = lean_apply_4(
        v_toBind_472_,
        lean_box(0),
        lean_box(0),
        v_getCallStack_474_,
        v___f_476_,
    );
    return v___x_477_;
}
pub unsafe fn l_Lake_guardCycle(
    mut v_00_u03ba_478_: *mut LeanObject,
    mut v_m_479_: *mut LeanObject,
    mut v_00_u03b1_480_: *mut LeanObject,
    mut v_inst_481_: *mut LeanObject,
    mut v_inst_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
    mut v_key_484_: *mut LeanObject,
    mut v_act_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMonadCallStack_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_throwCycle_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getCallStack_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_withCallStack_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v_toMonadCallStack_486_ = lean_ctor_get(v_inst_483_, 0);
    lean_inc_ref(v_toMonadCallStack_486_);
    v_toBind_487_ = lean_ctor_get(v_inst_482_, 1);
    lean_inc(v_toBind_487_);
    lean_dec_ref(v_inst_482_);
    v_throwCycle_488_ = lean_ctor_get(v_inst_483_, 1);
    lean_inc(v_throwCycle_488_);
    lean_dec_ref(v_inst_483_);
    v_getCallStack_489_ = lean_ctor_get(v_toMonadCallStack_486_, 0);
    lean_inc(v_getCallStack_489_);
    v_withCallStack_490_ = lean_ctor_get(v_toMonadCallStack_486_, 1);
    lean_inc(v_withCallStack_490_);
    lean_dec_ref(v_toMonadCallStack_486_);
    v___f_491_ = lean_alloc_closure(
        l_Lake_guardCycle___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_491_, 0, v_inst_481_);
    lean_closure_set(v___f_491_, 1, v_key_484_);
    lean_closure_set(v___f_491_, 2, v_withCallStack_490_);
    lean_closure_set(v___f_491_, 3, v_act_485_);
    lean_closure_set(v___f_491_, 4, v_throwCycle_488_);
    v___x_492_ = lean_apply_4(
        v_toBind_487_,
        lean_box(0),
        lean_box(0),
        v_getCallStack_489_,
        v___f_491_,
    );
    return v___x_492_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Cycle(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Cycle(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Cycle(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Cycle(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Cycle(builtin);
}
