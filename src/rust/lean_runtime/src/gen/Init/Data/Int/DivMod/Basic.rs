// Lean compiler output
// Module: Init.Data.Int.DivMod.Basic
// Imports: Init.Data.Int.Basic Init.Data.Nat.Div.Basic
use crate::r#gen::Init::Data::Int::Basic::{
    initialize_Init_Data_Int_Basic, l_Int_subNatNat, runtime_initialize_Init_Data_Int_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_lt, lean_int_neg, lean_int_neg_succ_of_nat, lean_int_sub,
    lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_div, lean_nat_mod, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Int_instDiv___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int_instDiv___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instDiv___closed__0_value) as *mut LeanObject;
pub static mut l_Int_instDiv: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instDiv___closed__0_value) as *mut LeanObject;
pub static l_Int_instMod___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Int_emod___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Int_instMod___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instMod___closed__0_value) as *mut LeanObject;
pub static mut l_Int_instMod: *mut LeanObject =
    core::ptr::addr_of!(l_Int_instMod___closed__0_value) as *mut LeanObject;
static mut l_Int_fdiv___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_fdiv___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int_bmod___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_bmod___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int_bmod___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_bmod___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Int_ediv___boxed(
    mut v_a_00___x40___internal___hyg_236_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = lean_int_ediv(
        v_a_00___x40___internal___hyg_236_,
        v_a_00___x40___internal___hyg_237_,
    );
    lean_dec(v_a_00___x40___internal___hyg_237_);
    lean_dec(v_a_00___x40___internal___hyg_236_);
    return v_res_238_;
}
pub unsafe fn l_Int_emod___boxed(
    mut v_a_00___x40___internal___hyg_241_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_243_: *mut LeanObject = core::ptr::null_mut();
    v_res_243_ = lean_int_emod(
        v_a_00___x40___internal___hyg_241_,
        v_a_00___x40___internal___hyg_242_,
    );
    lean_dec(v_a_00___x40___internal___hyg_242_);
    lean_dec(v_a_00___x40___internal___hyg_241_);
    return v_res_243_;
}
pub unsafe fn l_Int_divExact___boxed(
    mut v_x_251_: *mut LeanObject,
    mut v_y_252_: *mut LeanObject,
    mut v_h_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = lean_int_div_exact(v_x_251_, v_y_252_);
    lean_dec(v_y_252_);
    lean_dec(v_x_251_);
    return v_res_254_;
}
pub unsafe fn l_Int_tdiv___boxed(
    mut v_a_00___x40___internal___hyg_257_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_259_: *mut LeanObject = core::ptr::null_mut();
    v_res_259_ = lean_int_div(
        v_a_00___x40___internal___hyg_257_,
        v_a_00___x40___internal___hyg_258_,
    );
    lean_dec(v_a_00___x40___internal___hyg_258_);
    lean_dec(v_a_00___x40___internal___hyg_257_);
    return v_res_259_;
}
pub unsafe fn l_Int_tmod___boxed(
    mut v_a_00___x40___internal___hyg_262_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_264_: *mut LeanObject = core::ptr::null_mut();
    v_res_264_ = lean_int_mod(
        v_a_00___x40___internal___hyg_262_,
        v_a_00___x40___internal___hyg_263_,
    );
    lean_dec(v_a_00___x40___internal___hyg_263_);
    lean_dec(v_a_00___x40___internal___hyg_262_);
    return v_res_264_;
}
pub unsafe fn _init_l_Int_fdiv___closed__0() -> *mut LeanObject {
    let mut v_natZero_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_266_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_265_ = lean_unsigned_to_nat(0);
    v_intZero_266_ = lean_nat_to_int(v_natZero_265_);
    return v_intZero_266_;
}
pub unsafe fn l_Int_fdiv(
    mut v_x_267_: *mut LeanObject,
    mut v_x_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_m_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_278_: u8 = 0;
    let mut v_a_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_280_: u8 = 0;
    let mut v_isNeg_281_: u8 = 0;
    let mut v_a_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_292_: u8 = 0;
    let mut v_a_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_294_: u8 = 0;
    let mut v_n_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_natZero_276_ = lean_unsigned_to_nat(0);
                v_intZero_277_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_fdiv___closed__0),
                    core::ptr::addr_of_mut!(l_Int_fdiv___closed__0_once),
                    _init_l_Int_fdiv___closed__0,
                );
                v_isNeg_278_ = lean_int_dec_lt(v_x_267_, v_intZero_277_);
                if v_isNeg_278_ == 0 {
                    v_a_279_ = lean_nat_abs(v_x_267_);
                    v_isZero_280_ = lean_nat_dec_eq(v_a_279_, v_natZero_276_);
                    if v_isZero_280_ == 1 {
                        lean_dec(v_a_279_);
                        return v_intZero_277_;
                    } else {
                        v_isNeg_281_ = lean_int_dec_lt(v_x_268_, v_intZero_277_);
                        if v_isNeg_281_ == 0 {
                            v_a_282_ = lean_nat_abs(v_x_268_);
                            v___x_283_ = lean_nat_div(v_a_279_, v_a_282_);
                            lean_dec(v_a_282_);
                            lean_dec(v_a_279_);
                            v___x_284_ = lean_nat_to_int(v___x_283_);
                            return v___x_284_;
                        } else {
                            v_one_285_ = lean_unsigned_to_nat(1);
                            v_n_286_ = lean_nat_sub(v_a_279_, v_one_285_);
                            lean_dec(v_a_279_);
                            v_abs_287_ = lean_nat_abs(v_x_268_);
                            v_a_288_ = lean_nat_sub(v_abs_287_, v_one_285_);
                            lean_dec(v_abs_287_);
                            v_m_270_ = v_n_286_;
                            v_n_271_ = v_a_288_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_abs_289_ = lean_nat_abs(v_x_267_);
                    v_one_290_ = lean_unsigned_to_nat(1);
                    v_a_291_ = lean_nat_sub(v_abs_289_, v_one_290_);
                    lean_dec(v_abs_289_);
                    v_isNeg_292_ = lean_int_dec_lt(v_x_268_, v_intZero_277_);
                    if v_isNeg_292_ == 0 {
                        v_a_293_ = lean_nat_abs(v_x_268_);
                        v_isZero_294_ = lean_nat_dec_eq(v_a_293_, v_natZero_276_);
                        if v_isZero_294_ == 1 {
                            lean_dec(v_a_293_);
                            lean_dec(v_a_291_);
                            return v_intZero_277_;
                        } else {
                            v_n_295_ = lean_nat_sub(v_a_293_, v_one_290_);
                            lean_dec(v_a_293_);
                            v_m_270_ = v_a_291_;
                            v_n_271_ = v_n_295_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_abs_296_ = lean_nat_abs(v_x_268_);
                        v_a_297_ = lean_nat_sub(v_abs_296_, v_one_290_);
                        lean_dec(v_abs_296_);
                        v___x_298_ = lean_nat_add(v_a_291_, v_one_290_);
                        lean_dec(v_a_291_);
                        v___x_299_ = lean_nat_add(v_a_297_, v_one_290_);
                        lean_dec(v_a_297_);
                        v___x_300_ = lean_nat_div(v___x_298_, v___x_299_);
                        lean_dec(v___x_299_);
                        lean_dec(v___x_298_);
                        v___x_301_ = lean_nat_to_int(v___x_300_);
                        return v___x_301_;
                    }
                }
            }
            1 => {
                v___x_272_ = lean_unsigned_to_nat(1);
                v___x_273_ = lean_nat_add(v_n_271_, v___x_272_);
                lean_dec(v_n_271_);
                v___x_274_ = lean_nat_div(v_m_270_, v___x_273_);
                lean_dec(v___x_273_);
                lean_dec(v_m_270_);
                v___x_275_ = lean_int_neg_succ_of_nat(v___x_274_);
                return v___x_275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_fdiv___boxed(
    mut v_x_302_: *mut LeanObject,
    mut v_x_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_304_ = l_Int_fdiv(v_x_302_, v_x_303_);
    lean_dec(v_x_303_);
    lean_dec(v_x_302_);
    return v_res_304_;
}
pub unsafe fn l_Int_fmod(
    mut v_x_305_: *mut LeanObject,
    mut v_x_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_309_: u8 = 0;
    v_natZero_307_ = lean_unsigned_to_nat(0);
    v_intZero_308_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_fdiv___closed__0),
        core::ptr::addr_of_mut!(l_Int_fdiv___closed__0_once),
        _init_l_Int_fdiv___closed__0,
    );
    v_isNeg_309_ = lean_int_dec_lt(v_x_305_, v_intZero_308_);
    if v_isNeg_309_ == 0 {
        let mut v_a_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_311_: u8 = 0;
        v_a_310_ = lean_nat_abs(v_x_305_);
        v_isZero_311_ = lean_nat_dec_eq(v_a_310_, v_natZero_307_);
        if v_isZero_311_ == 1 {
            lean_dec(v_a_310_);
            return v_intZero_308_;
        } else {
            let mut v_isNeg_312_: u8 = 0;
            v_isNeg_312_ = lean_int_dec_lt(v_x_306_, v_intZero_308_);
            if v_isNeg_312_ == 0 {
                let mut v_a_313_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
                v_a_313_ = lean_nat_abs(v_x_306_);
                v___x_314_ = lean_nat_mod(v_a_310_, v_a_313_);
                lean_dec(v_a_313_);
                lean_dec(v_a_310_);
                v___x_315_ = lean_nat_to_int(v___x_314_);
                return v___x_315_;
            } else {
                let mut v_one_316_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_317_: *mut LeanObject = core::ptr::null_mut();
                let mut v_abs_318_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_319_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
                v_one_316_ = lean_unsigned_to_nat(1);
                v_n_317_ = lean_nat_sub(v_a_310_, v_one_316_);
                lean_dec(v_a_310_);
                v_abs_318_ = lean_nat_abs(v_x_306_);
                v_a_319_ = lean_nat_sub(v_abs_318_, v_one_316_);
                lean_dec(v_abs_318_);
                v___x_320_ = lean_nat_add(v_a_319_, v_one_316_);
                v___x_321_ = lean_nat_mod(v_n_317_, v___x_320_);
                lean_dec(v___x_320_);
                lean_dec(v_n_317_);
                v___x_322_ = l_Int_subNatNat(v___x_321_, v_a_319_);
                lean_dec(v_a_319_);
                lean_dec(v___x_321_);
                return v___x_322_;
            }
        }
    } else {
        let mut v_abs_323_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_324_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_325_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_326_: u8 = 0;
        v_abs_323_ = lean_nat_abs(v_x_305_);
        v_one_324_ = lean_unsigned_to_nat(1);
        v_a_325_ = lean_nat_sub(v_abs_323_, v_one_324_);
        lean_dec(v_abs_323_);
        v_isNeg_326_ = lean_int_dec_lt(v_x_306_, v_intZero_308_);
        if v_isNeg_326_ == 0 {
            let mut v_a_327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
            v_a_327_ = lean_nat_abs(v_x_306_);
            v___x_328_ = lean_nat_mod(v_a_325_, v_a_327_);
            lean_dec(v_a_325_);
            v___x_329_ = lean_nat_add(v___x_328_, v_one_324_);
            lean_dec(v___x_328_);
            v___x_330_ = l_Int_subNatNat(v_a_327_, v___x_329_);
            lean_dec(v___x_329_);
            lean_dec(v_a_327_);
            return v___x_330_;
        } else {
            let mut v_abs_331_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
            v_abs_331_ = lean_nat_abs(v_x_306_);
            v_a_332_ = lean_nat_sub(v_abs_331_, v_one_324_);
            lean_dec(v_abs_331_);
            v___x_333_ = lean_nat_add(v_a_325_, v_one_324_);
            lean_dec(v_a_325_);
            v___x_334_ = lean_nat_add(v_a_332_, v_one_324_);
            lean_dec(v_a_332_);
            v___x_335_ = lean_nat_mod(v___x_333_, v___x_334_);
            lean_dec(v___x_334_);
            lean_dec(v___x_333_);
            v___x_336_ = lean_nat_to_int(v___x_335_);
            v___x_337_ = lean_int_neg(v___x_336_);
            lean_dec(v___x_336_);
            return v___x_337_;
        }
    }
}
pub unsafe fn l_Int_fmod___boxed(
    mut v_x_338_: *mut LeanObject,
    mut v_x_339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_340_: *mut LeanObject = core::ptr::null_mut();
    v_res_340_ = l_Int_fmod(v_x_338_, v_x_339_);
    lean_dec(v_x_339_);
    lean_dec(v_x_338_);
    return v_res_340_;
}
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_342_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_341_ = lean_unsigned_to_nat(0);
    v_intZero_342_ = lean_nat_to_int(v_natZero_341_);
    return v_intZero_342_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(
    mut v_x_343_: *mut LeanObject,
    mut v_x_344_: *mut LeanObject,
    mut v_h__1_345_: *mut LeanObject,
    mut v_h__2_346_: *mut LeanObject,
    mut v_h__3_347_: *mut LeanObject,
    mut v_h__4_348_: *mut LeanObject,
    mut v_h__5_349_: *mut LeanObject,
    mut v_h__6_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_353_: u8 = 0;
    v_natZero_351_ = lean_unsigned_to_nat(0);
    v_intZero_352_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_353_ = lean_int_dec_lt(v_x_343_, v_intZero_352_);
    if v_isNeg_353_ == 0 {
        let mut v_a_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_355_: u8 = 0;
        lean_dec(v_h__6_350_);
        lean_dec(v_h__5_349_);
        lean_dec(v_h__4_348_);
        v_a_354_ = lean_nat_abs(v_x_343_);
        v_isZero_355_ = lean_nat_dec_eq(v_a_354_, v_natZero_351_);
        if v_isZero_355_ == 1 {
            let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_354_);
            lean_dec(v_h__3_347_);
            lean_dec(v_h__2_346_);
            v___x_356_ = lean_apply_1(v_h__1_345_, v_x_344_);
            return v___x_356_;
        } else {
            let mut v_isNeg_357_: u8 = 0;
            lean_dec(v_h__1_345_);
            v_isNeg_357_ = lean_int_dec_lt(v_x_344_, v_intZero_352_);
            if v_isNeg_357_ == 0 {
                let mut v_a_358_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_347_);
                v_a_358_ = lean_nat_abs(v_x_344_);
                lean_dec(v_x_344_);
                v___x_359_ = lean_apply_3(v_h__2_346_, v_a_354_, v_a_358_, lean_box(0));
                return v___x_359_;
            } else {
                let mut v_one_360_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_361_: *mut LeanObject = core::ptr::null_mut();
                let mut v_abs_362_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_346_);
                v_one_360_ = lean_unsigned_to_nat(1);
                v_n_361_ = lean_nat_sub(v_a_354_, v_one_360_);
                lean_dec(v_a_354_);
                v_abs_362_ = lean_nat_abs(v_x_344_);
                lean_dec(v_x_344_);
                v_a_363_ = lean_nat_sub(v_abs_362_, v_one_360_);
                lean_dec(v_abs_362_);
                v___x_364_ = lean_apply_2(v_h__3_347_, v_n_361_, v_a_363_);
                return v___x_364_;
            }
        }
    } else {
        let mut v_abs_365_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_366_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_367_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_368_: u8 = 0;
        lean_dec(v_h__3_347_);
        lean_dec(v_h__2_346_);
        lean_dec(v_h__1_345_);
        v_abs_365_ = lean_nat_abs(v_x_343_);
        v_one_366_ = lean_unsigned_to_nat(1);
        v_a_367_ = lean_nat_sub(v_abs_365_, v_one_366_);
        lean_dec(v_abs_365_);
        v_isNeg_368_ = lean_int_dec_lt(v_x_344_, v_intZero_352_);
        if v_isNeg_368_ == 0 {
            let mut v_a_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isZero_370_: u8 = 0;
            lean_dec(v_h__6_350_);
            v_a_369_ = lean_nat_abs(v_x_344_);
            lean_dec(v_x_344_);
            v_isZero_370_ = lean_nat_dec_eq(v_a_369_, v_natZero_351_);
            if v_isZero_370_ == 1 {
                let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_a_369_);
                lean_dec(v_h__5_349_);
                v___x_371_ = lean_apply_1(v_h__4_348_, v_a_367_);
                return v___x_371_;
            } else {
                let mut v_n_372_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_348_);
                v_n_372_ = lean_nat_sub(v_a_369_, v_one_366_);
                lean_dec(v_a_369_);
                v___x_373_ = lean_apply_2(v_h__5_349_, v_a_367_, v_n_372_);
                return v___x_373_;
            }
        } else {
            let mut v_abs_374_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_375_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_349_);
            lean_dec(v_h__4_348_);
            v_abs_374_ = lean_nat_abs(v_x_344_);
            lean_dec(v_x_344_);
            v_a_375_ = lean_nat_sub(v_abs_374_, v_one_366_);
            lean_dec(v_abs_374_);
            v___x_376_ = lean_apply_2(v_h__6_350_, v_a_367_, v_a_375_);
            return v___x_376_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___boxed(
    mut v_x_377_: *mut LeanObject,
    mut v_x_378_: *mut LeanObject,
    mut v_h__1_379_: *mut LeanObject,
    mut v_h__2_380_: *mut LeanObject,
    mut v_h__3_381_: *mut LeanObject,
    mut v_h__4_382_: *mut LeanObject,
    mut v_h__5_383_: *mut LeanObject,
    mut v_h__6_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_385_: *mut LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg(
        v_x_377_,
        v_x_378_,
        v_h__1_379_,
        v_h__2_380_,
        v_h__3_381_,
        v_h__4_382_,
        v_h__5_383_,
        v_h__6_384_,
    );
    lean_dec(v_x_377_);
    return v_res_385_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(
    mut v_motive_386_: *mut LeanObject,
    mut v_x_387_: *mut LeanObject,
    mut v_x_388_: *mut LeanObject,
    mut v_h__1_389_: *mut LeanObject,
    mut v_h__2_390_: *mut LeanObject,
    mut v_h__3_391_: *mut LeanObject,
    mut v_h__4_392_: *mut LeanObject,
    mut v_h__5_393_: *mut LeanObject,
    mut v_h__6_394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_397_: u8 = 0;
    v_natZero_395_ = lean_unsigned_to_nat(0);
    v_intZero_396_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_397_ = lean_int_dec_lt(v_x_387_, v_intZero_396_);
    if v_isNeg_397_ == 0 {
        let mut v_a_398_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_399_: u8 = 0;
        lean_dec(v_h__6_394_);
        lean_dec(v_h__5_393_);
        lean_dec(v_h__4_392_);
        v_a_398_ = lean_nat_abs(v_x_387_);
        v_isZero_399_ = lean_nat_dec_eq(v_a_398_, v_natZero_395_);
        if v_isZero_399_ == 1 {
            let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_398_);
            lean_dec(v_h__3_391_);
            lean_dec(v_h__2_390_);
            v___x_400_ = lean_apply_1(v_h__1_389_, v_x_388_);
            return v___x_400_;
        } else {
            let mut v_isNeg_401_: u8 = 0;
            lean_dec(v_h__1_389_);
            v_isNeg_401_ = lean_int_dec_lt(v_x_388_, v_intZero_396_);
            if v_isNeg_401_ == 0 {
                let mut v_a_402_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_391_);
                v_a_402_ = lean_nat_abs(v_x_388_);
                lean_dec(v_x_388_);
                v___x_403_ = lean_apply_3(v_h__2_390_, v_a_398_, v_a_402_, lean_box(0));
                return v___x_403_;
            } else {
                let mut v_one_404_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_405_: *mut LeanObject = core::ptr::null_mut();
                let mut v_abs_406_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_407_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_390_);
                v_one_404_ = lean_unsigned_to_nat(1);
                v_n_405_ = lean_nat_sub(v_a_398_, v_one_404_);
                lean_dec(v_a_398_);
                v_abs_406_ = lean_nat_abs(v_x_388_);
                lean_dec(v_x_388_);
                v_a_407_ = lean_nat_sub(v_abs_406_, v_one_404_);
                lean_dec(v_abs_406_);
                v___x_408_ = lean_apply_2(v_h__3_391_, v_n_405_, v_a_407_);
                return v___x_408_;
            }
        }
    } else {
        let mut v_abs_409_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_410_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_411_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_412_: u8 = 0;
        lean_dec(v_h__3_391_);
        lean_dec(v_h__2_390_);
        lean_dec(v_h__1_389_);
        v_abs_409_ = lean_nat_abs(v_x_387_);
        v_one_410_ = lean_unsigned_to_nat(1);
        v_a_411_ = lean_nat_sub(v_abs_409_, v_one_410_);
        lean_dec(v_abs_409_);
        v_isNeg_412_ = lean_int_dec_lt(v_x_388_, v_intZero_396_);
        if v_isNeg_412_ == 0 {
            let mut v_a_413_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isZero_414_: u8 = 0;
            lean_dec(v_h__6_394_);
            v_a_413_ = lean_nat_abs(v_x_388_);
            lean_dec(v_x_388_);
            v_isZero_414_ = lean_nat_dec_eq(v_a_413_, v_natZero_395_);
            if v_isZero_414_ == 1 {
                let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_a_413_);
                lean_dec(v_h__5_393_);
                v___x_415_ = lean_apply_1(v_h__4_392_, v_a_411_);
                return v___x_415_;
            } else {
                let mut v_n_416_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_392_);
                v_n_416_ = lean_nat_sub(v_a_413_, v_one_410_);
                lean_dec(v_a_413_);
                v___x_417_ = lean_apply_2(v_h__5_393_, v_a_411_, v_n_416_);
                return v___x_417_;
            }
        } else {
            let mut v_abs_418_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__5_393_);
            lean_dec(v_h__4_392_);
            v_abs_418_ = lean_nat_abs(v_x_388_);
            lean_dec(v_x_388_);
            v_a_419_ = lean_nat_sub(v_abs_418_, v_one_410_);
            lean_dec(v_abs_418_);
            v___x_420_ = lean_apply_2(v_h__6_394_, v_a_411_, v_a_419_);
            return v___x_420_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___boxed(
    mut v_motive_421_: *mut LeanObject,
    mut v_x_422_: *mut LeanObject,
    mut v_x_423_: *mut LeanObject,
    mut v_h__1_424_: *mut LeanObject,
    mut v_h__2_425_: *mut LeanObject,
    mut v_h__3_426_: *mut LeanObject,
    mut v_h__4_427_: *mut LeanObject,
    mut v_h__5_428_: *mut LeanObject,
    mut v_h__6_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_430_: *mut LeanObject = core::ptr::null_mut();
    v_res_430_ = l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter(
        v_motive_421_,
        v_x_422_,
        v_x_423_,
        v_h__1_424_,
        v_h__2_425_,
        v_h__3_426_,
        v_h__4_427_,
        v_h__5_428_,
        v_h__6_429_,
    );
    lean_dec(v_x_422_);
    return v_res_430_;
}
pub unsafe fn l_Nat_cast___at___00Int_bmod_spec__0(
    mut v_a_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    v___x_432_ = lean_nat_to_int(v_a_431_);
    return v___x_432_;
}
pub unsafe fn _init_l_Int_bmod___closed__0() -> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = lean_unsigned_to_nat(1);
    v___x_434_ = lean_nat_to_int(v___x_433_);
    return v___x_434_;
}
pub unsafe fn _init_l_Int_bmod___closed__1() -> *mut LeanObject {
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_435_ = lean_unsigned_to_nat(2);
    v___x_436_ = lean_nat_to_int(v___x_435_);
    return v___x_436_;
}
pub unsafe fn l_Int_bmod(
    mut v_x_437_: *mut LeanObject,
    mut v_m_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: u8 = 0;
    v___x_439_ = lean_nat_to_int(v_m_438_);
    v_r_440_ = lean_int_emod(v_x_437_, v___x_439_);
    v___x_441_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_bmod___closed__0),
        core::ptr::addr_of_mut!(l_Int_bmod___closed__0_once),
        _init_l_Int_bmod___closed__0,
    );
    v___x_442_ = lean_int_add(v___x_439_, v___x_441_);
    v___x_443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_bmod___closed__1),
        core::ptr::addr_of_mut!(l_Int_bmod___closed__1_once),
        _init_l_Int_bmod___closed__1,
    );
    v___x_444_ = lean_int_ediv(v___x_442_, v___x_443_);
    lean_dec(v___x_442_);
    v___x_445_ = lean_int_dec_lt(v_r_440_, v___x_444_);
    lean_dec(v___x_444_);
    if v___x_445_ == 0 {
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        v___x_446_ = lean_int_sub(v_r_440_, v___x_439_);
        lean_dec(v___x_439_);
        lean_dec(v_r_440_);
        return v___x_446_;
    } else {
        lean_dec(v___x_439_);
        return v_r_440_;
    }
}
pub unsafe fn l_Int_bmod___boxed(
    mut v_x_447_: *mut LeanObject,
    mut v_m_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Int_bmod(v_x_447_, v_m_448_);
    lean_dec(v_x_447_);
    return v_res_449_;
}
pub unsafe fn l_Int_bdiv(
    mut v_x_450_: *mut LeanObject,
    mut v_m_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u8 = 0;
    v___x_452_ = lean_unsigned_to_nat(0);
    v___x_453_ = lean_nat_dec_eq(v_m_451_, v___x_452_);
    if v___x_453_ == 0 {
        let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
        let mut v_q_455_: *mut LeanObject = core::ptr::null_mut();
        let mut v_r_456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_461_: u8 = 0;
        v___x_454_ = lean_nat_to_int(v_m_451_);
        v_q_455_ = lean_int_ediv(v_x_450_, v___x_454_);
        v_r_456_ = lean_int_emod(v_x_450_, v___x_454_);
        v___x_457_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_bmod___closed__0),
            core::ptr::addr_of_mut!(l_Int_bmod___closed__0_once),
            _init_l_Int_bmod___closed__0,
        );
        v___x_458_ = lean_int_add(v___x_454_, v___x_457_);
        lean_dec(v___x_454_);
        v___x_459_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_bmod___closed__1),
            core::ptr::addr_of_mut!(l_Int_bmod___closed__1_once),
            _init_l_Int_bmod___closed__1,
        );
        v___x_460_ = lean_int_ediv(v___x_458_, v___x_459_);
        lean_dec(v___x_458_);
        v___x_461_ = lean_int_dec_lt(v_r_456_, v___x_460_);
        lean_dec(v___x_460_);
        lean_dec(v_r_456_);
        if v___x_461_ == 0 {
            let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
            v___x_462_ = lean_int_add(v_q_455_, v___x_457_);
            lean_dec(v_q_455_);
            return v___x_462_;
        } else {
            return v_q_455_;
        }
    } else {
        let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_m_451_);
        v___x_463_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Basic_0__Int_fdiv_match__1_splitter___redArg___closed__0);
        return v___x_463_;
    }
}
pub unsafe fn l_Int_bdiv___boxed(
    mut v_x_464_: *mut LeanObject,
    mut v_m_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_466_: *mut LeanObject = core::ptr::null_mut();
    v_res_466_ = l_Int_bdiv(v_x_464_, v_m_465_);
    lean_dec(v_x_464_);
    return v_res_466_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_DivMod_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_DivMod_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_DivMod_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_DivMod_Basic(builtin);
}
