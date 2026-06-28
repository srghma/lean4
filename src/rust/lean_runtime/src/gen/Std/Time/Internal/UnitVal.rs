// Lean compiler output
// Module: Std.Time.Internal.UnitVal
// Imports: Init.Data.Order.Ord Init.Data.Rat.Basic
use crate::r#gen::Init::Data::Int::Basic::l_Int_neg___boxed;
use crate::r#gen::Init::Data::Int::Repr::{l_Int_repr, l_Int_repr___boxed};
use crate::r#gen::Init::Data::Order::Ord::{
    initialize_Init_Data_Order_Ord, runtime_initialize_Init_Data_Order_Ord,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    initialize_Init_Data_Rat_Basic, l_Rat_div, runtime_initialize_Init_Data_Rat_Basic,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_sub,
    lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_div, lean_int_ediv};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Internal_instOrdUnitVal___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Internal_instOrdUnitVal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_instOrdUnitVal___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Internal_UnitVal_instRepr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Internal_UnitVal_instRepr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_UnitVal_instRepr___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Internal_UnitVal_instNeg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Internal_UnitVal_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_UnitVal_instNeg___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Internal_UnitVal_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_repr___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Internal_UnitVal_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_UnitVal_instToString___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0() -> *mut LeanObject
{
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    v___x_263_ = lean_unsigned_to_nat(0);
    v___x_264_ = lean_nat_to_int(v___x_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Time_Internal_instInhabitedUnitVal_default(
    mut v_00_u03b1_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once),
        _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0,
    );
    return v___x_266_;
}
pub unsafe fn l_Std_Time_Internal_instInhabitedUnitVal_default___boxed(
    mut v_00_u03b1_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v_00_u03b1_267_);
    lean_dec_ref(v_00_u03b1_267_);
    return v_res_268_;
}
pub unsafe fn l_Std_Time_Internal_instInhabitedUnitVal(
    mut v_a_269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = l_Std_Time_Internal_instInhabitedUnitVal_default(v_a_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_Time_Internal_instInhabitedUnitVal___boxed(
    mut v_a_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_272_: *mut LeanObject = core::ptr::null_mut();
    v_res_272_ = l_Std_Time_Internal_instInhabitedUnitVal(v_a_271_);
    lean_dec_ref(v_a_271_);
    return v_res_272_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg(
    mut v_x_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
) -> u8 {
    let mut v___x_275_: u8 = 0;
    v___x_275_ = lean_int_dec_eq(v_x_273_, v_x_274_);
    return v___x_275_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg___boxed(
    mut v_x_276_: *mut LeanObject,
    mut v_x_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: u8 = 0;
    let mut v_r_279_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_Time_Internal_instDecidableEqUnitVal_decEq___redArg(v_x_276_, v_x_277_);
    lean_dec(v_x_277_);
    lean_dec(v_x_276_);
    v_r_279_ = lean_box((v_res_278_) as usize);
    return v_r_279_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal_decEq(
    mut v_00_u03b1_280_: *mut LeanObject,
    mut v_x_281_: *mut LeanObject,
    mut v_x_282_: *mut LeanObject,
) -> u8 {
    let mut v___x_283_: u8 = 0;
    v___x_283_ = lean_int_dec_eq(v_x_281_, v_x_282_);
    return v___x_283_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal_decEq___boxed(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_x_285_: *mut LeanObject,
    mut v_x_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_287_: u8 = 0;
    let mut v_r_288_: *mut LeanObject = core::ptr::null_mut();
    v_res_287_ =
        l_Std_Time_Internal_instDecidableEqUnitVal_decEq(v_00_u03b1_284_, v_x_285_, v_x_286_);
    lean_dec(v_x_286_);
    lean_dec(v_x_285_);
    lean_dec_ref(v_00_u03b1_284_);
    v_r_288_ = lean_box((v_res_287_) as usize);
    return v_r_288_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal___redArg(
    mut v_x_289_: *mut LeanObject,
    mut v_x_290_: *mut LeanObject,
) -> u8 {
    let mut v___x_291_: u8 = 0;
    v___x_291_ = lean_int_dec_eq(v_x_289_, v_x_290_);
    return v___x_291_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal___redArg___boxed(
    mut v_x_292_: *mut LeanObject,
    mut v_x_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_294_: u8 = 0;
    let mut v_r_295_: *mut LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Time_Internal_instDecidableEqUnitVal___redArg(v_x_292_, v_x_293_);
    lean_dec(v_x_293_);
    lean_dec(v_x_292_);
    v_r_295_ = lean_box((v_res_294_) as usize);
    return v_r_295_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
    mut v_x_298_: *mut LeanObject,
) -> u8 {
    let mut v___x_299_: u8 = 0;
    v___x_299_ = lean_int_dec_eq(v_x_297_, v_x_298_);
    return v___x_299_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableEqUnitVal___boxed(
    mut v_00_u03b1_300_: *mut LeanObject,
    mut v_x_301_: *mut LeanObject,
    mut v_x_302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_303_: u8 = 0;
    let mut v_r_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Std_Time_Internal_instDecidableEqUnitVal(v_00_u03b1_300_, v_x_301_, v_x_302_);
    lean_dec(v_x_302_);
    lean_dec(v_x_301_);
    lean_dec_ref(v_00_u03b1_300_);
    v_r_304_ = lean_box((v_res_303_) as usize);
    return v_r_304_;
}
pub unsafe fn l_Std_Time_Internal_instLEUnitVal(mut v_x_305_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    v___x_306_ = lean_box(0);
    return v___x_306_;
}
pub unsafe fn l_Std_Time_Internal_instLEUnitVal___boxed(
    mut v_x_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Std_Time_Internal_instLEUnitVal(v_x_307_);
    lean_dec_ref(v_x_307_);
    return v_res_308_;
}
pub unsafe fn l_Std_Time_Internal_instOrdUnitVal___lam__0(
    mut v_x_309_: *mut LeanObject,
    mut v_y_310_: *mut LeanObject,
) -> u8 {
    let mut v___x_311_: u8 = 0;
    v___x_311_ = lean_int_dec_lt(v_x_309_, v_y_310_);
    if v___x_311_ == 0 {
        let mut v___x_312_: u8 = 0;
        v___x_312_ = lean_int_dec_eq(v_x_309_, v_y_310_);
        if v___x_312_ == 0 {
            let mut v___x_313_: u8 = 0;
            v___x_313_ = 2;
            return v___x_313_;
        } else {
            let mut v___x_314_: u8 = 0;
            v___x_314_ = 1;
            return v___x_314_;
        }
    } else {
        let mut v___x_315_: u8 = 0;
        v___x_315_ = 0;
        return v___x_315_;
    }
}
pub unsafe fn l_Std_Time_Internal_instOrdUnitVal___lam__0___boxed(
    mut v_x_316_: *mut LeanObject,
    mut v_y_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_318_: u8 = 0;
    let mut v_r_319_: *mut LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Time_Internal_instOrdUnitVal___lam__0(v_x_316_, v_y_317_);
    lean_dec(v_y_317_);
    lean_dec(v_x_316_);
    v_r_319_ = lean_box((v_res_318_) as usize);
    return v_r_319_;
}
pub unsafe fn l_Std_Time_Internal_instOrdUnitVal(mut v_x_321_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_322_: *mut LeanObject = core::ptr::null_mut();
    v___f_322_ = l_Std_Time_Internal_instOrdUnitVal___closed__0;
    return v___f_322_;
}
pub unsafe fn l_Std_Time_Internal_instOrdUnitVal___boxed(
    mut v_x_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_324_: *mut LeanObject = core::ptr::null_mut();
    v_res_324_ = l_Std_Time_Internal_instOrdUnitVal(v_x_323_);
    lean_dec_ref(v_x_323_);
    return v_res_324_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableLeUnitVal___redArg(
    mut v_x_325_: *mut LeanObject,
    mut v_y_326_: *mut LeanObject,
) -> u8 {
    let mut v___x_327_: u8 = 0;
    v___x_327_ = lean_int_dec_le(v_x_325_, v_y_326_);
    return v___x_327_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableLeUnitVal___redArg___boxed(
    mut v_x_328_: *mut LeanObject,
    mut v_y_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_330_: u8 = 0;
    let mut v_r_331_: *mut LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Std_Time_Internal_instDecidableLeUnitVal___redArg(v_x_328_, v_y_329_);
    lean_dec(v_y_329_);
    lean_dec(v_x_328_);
    v_r_331_ = lean_box((v_res_330_) as usize);
    return v_r_331_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableLeUnitVal(
    mut v_z_332_: *mut LeanObject,
    mut v_x_333_: *mut LeanObject,
    mut v_y_334_: *mut LeanObject,
) -> u8 {
    let mut v___x_335_: u8 = 0;
    v___x_335_ = lean_int_dec_le(v_x_333_, v_y_334_);
    return v___x_335_;
}
pub unsafe fn l_Std_Time_Internal_instDecidableLeUnitVal___boxed(
    mut v_z_336_: *mut LeanObject,
    mut v_x_337_: *mut LeanObject,
    mut v_y_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: u8 = 0;
    let mut v_r_340_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Time_Internal_instDecidableLeUnitVal(v_z_336_, v_x_337_, v_y_338_);
    lean_dec(v_y_338_);
    lean_dec(v_x_337_);
    lean_dec_ref(v_z_336_);
    v_r_340_ = lean_box((v_res_339_) as usize);
    return v_r_340_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ofNat___redArg(
    mut v_value_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = lean_nat_to_int(v_value_341_);
    return v___x_342_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ofNat(
    mut v_00_u03b1_343_: *mut LeanObject,
    mut v_value_344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_345_ = lean_nat_to_int(v_value_344_);
    return v___x_345_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ofNat___boxed(
    mut v_00_u03b1_346_: *mut LeanObject,
    mut v_value_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_348_: *mut LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Std_Time_Internal_UnitVal_ofNat(v_00_u03b1_346_, v_value_347_);
    lean_dec_ref(v_00_u03b1_346_);
    return v_res_348_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_toInt___redArg(
    mut v_unit_349_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_unit_349_);
    return v_unit_349_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_toInt___redArg___boxed(
    mut v_unit_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_Std_Time_Internal_UnitVal_toInt___redArg(v_unit_350_);
    lean_dec(v_unit_350_);
    return v_res_351_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_toInt(
    mut v_00_u03b1_352_: *mut LeanObject,
    mut v_unit_353_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_unit_353_);
    return v_unit_353_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_toInt___boxed(
    mut v_00_u03b1_354_: *mut LeanObject,
    mut v_unit_355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_356_: *mut LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Time_Internal_UnitVal_toInt(v_00_u03b1_354_, v_unit_355_);
    lean_dec(v_unit_355_);
    lean_dec_ref(v_00_u03b1_354_);
    return v_res_356_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_mul___redArg(
    mut v_unit_357_: *mut LeanObject,
    mut v_factor_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_int_mul(v_unit_357_, v_factor_358_);
    return v___x_359_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_mul___redArg___boxed(
    mut v_unit_360_: *mut LeanObject,
    mut v_factor_361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_362_: *mut LeanObject = core::ptr::null_mut();
    v_res_362_ = l_Std_Time_Internal_UnitVal_mul___redArg(v_unit_360_, v_factor_361_);
    lean_dec(v_factor_361_);
    lean_dec(v_unit_360_);
    return v_res_362_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_mul(
    mut v_a_363_: *mut LeanObject,
    mut v_unit_364_: *mut LeanObject,
    mut v_factor_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = lean_int_mul(v_unit_364_, v_factor_365_);
    return v___x_366_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_mul___boxed(
    mut v_a_367_: *mut LeanObject,
    mut v_unit_368_: *mut LeanObject,
    mut v_factor_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_370_: *mut LeanObject = core::ptr::null_mut();
    v_res_370_ = l_Std_Time_Internal_UnitVal_mul(v_a_367_, v_unit_368_, v_factor_369_);
    lean_dec(v_factor_369_);
    lean_dec(v_unit_368_);
    lean_dec_ref(v_a_367_);
    return v_res_370_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ediv___redArg(
    mut v_unit_371_: *mut LeanObject,
    mut v_divisor_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_int_ediv(v_unit_371_, v_divisor_372_);
    return v___x_373_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ediv___redArg___boxed(
    mut v_unit_374_: *mut LeanObject,
    mut v_divisor_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_376_: *mut LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Std_Time_Internal_UnitVal_ediv___redArg(v_unit_374_, v_divisor_375_);
    lean_dec(v_divisor_375_);
    lean_dec(v_unit_374_);
    return v_res_376_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ediv(
    mut v_a_377_: *mut LeanObject,
    mut v_unit_378_: *mut LeanObject,
    mut v_divisor_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v___x_380_ = lean_int_ediv(v_unit_378_, v_divisor_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_ediv___boxed(
    mut v_a_381_: *mut LeanObject,
    mut v_unit_382_: *mut LeanObject,
    mut v_divisor_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_Time_Internal_UnitVal_ediv(v_a_381_, v_unit_382_, v_divisor_383_);
    lean_dec(v_divisor_383_);
    lean_dec(v_unit_382_);
    lean_dec_ref(v_a_381_);
    return v_res_384_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_tdiv___redArg(
    mut v_unit_385_: *mut LeanObject,
    mut v_divisor_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_int_div(v_unit_385_, v_divisor_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_tdiv___redArg___boxed(
    mut v_unit_388_: *mut LeanObject,
    mut v_divisor_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_390_: *mut LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Std_Time_Internal_UnitVal_tdiv___redArg(v_unit_388_, v_divisor_389_);
    lean_dec(v_divisor_389_);
    lean_dec(v_unit_388_);
    return v_res_390_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_tdiv(
    mut v_a_391_: *mut LeanObject,
    mut v_unit_392_: *mut LeanObject,
    mut v_divisor_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_int_div(v_unit_392_, v_divisor_393_);
    return v___x_394_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_tdiv___boxed(
    mut v_a_395_: *mut LeanObject,
    mut v_unit_396_: *mut LeanObject,
    mut v_divisor_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_398_: *mut LeanObject = core::ptr::null_mut();
    v_res_398_ = l_Std_Time_Internal_UnitVal_tdiv(v_a_395_, v_unit_396_, v_divisor_397_);
    lean_dec(v_divisor_397_);
    lean_dec(v_unit_396_);
    lean_dec_ref(v_a_395_);
    return v_res_398_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_div___redArg(
    mut v_unit_399_: *mut LeanObject,
    mut v_divisor_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = lean_int_div(v_unit_399_, v_divisor_400_);
    return v___x_401_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_div___redArg___boxed(
    mut v_unit_402_: *mut LeanObject,
    mut v_divisor_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_404_: *mut LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Std_Time_Internal_UnitVal_div___redArg(v_unit_402_, v_divisor_403_);
    lean_dec(v_divisor_403_);
    lean_dec(v_unit_402_);
    return v_res_404_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_div(
    mut v_a_405_: *mut LeanObject,
    mut v_unit_406_: *mut LeanObject,
    mut v_divisor_407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    v___x_408_ = lean_int_div(v_unit_406_, v_divisor_407_);
    return v___x_408_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_div___boxed(
    mut v_a_409_: *mut LeanObject,
    mut v_unit_410_: *mut LeanObject,
    mut v_divisor_411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_412_: *mut LeanObject = core::ptr::null_mut();
    v_res_412_ = l_Std_Time_Internal_UnitVal_div(v_a_409_, v_unit_410_, v_divisor_411_);
    lean_dec(v_divisor_411_);
    lean_dec(v_unit_410_);
    lean_dec_ref(v_a_409_);
    return v_res_412_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_add___redArg(
    mut v_u1_413_: *mut LeanObject,
    mut v_u2_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v___x_415_ = lean_int_add(v_u1_413_, v_u2_414_);
    return v___x_415_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_add___redArg___boxed(
    mut v_u1_416_: *mut LeanObject,
    mut v_u2_417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_418_: *mut LeanObject = core::ptr::null_mut();
    v_res_418_ = l_Std_Time_Internal_UnitVal_add___redArg(v_u1_416_, v_u2_417_);
    lean_dec(v_u2_417_);
    lean_dec(v_u1_416_);
    return v_res_418_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_add(
    mut v_00_u03b1_419_: *mut LeanObject,
    mut v_u1_420_: *mut LeanObject,
    mut v_u2_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    v___x_422_ = lean_int_add(v_u1_420_, v_u2_421_);
    return v___x_422_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_add___boxed(
    mut v_00_u03b1_423_: *mut LeanObject,
    mut v_u1_424_: *mut LeanObject,
    mut v_u2_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_426_: *mut LeanObject = core::ptr::null_mut();
    v_res_426_ = l_Std_Time_Internal_UnitVal_add(v_00_u03b1_423_, v_u1_424_, v_u2_425_);
    lean_dec(v_u2_425_);
    lean_dec(v_u1_424_);
    lean_dec_ref(v_00_u03b1_423_);
    return v_res_426_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_sub___redArg(
    mut v_u1_427_: *mut LeanObject,
    mut v_u2_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    v___x_429_ = lean_int_sub(v_u1_427_, v_u2_428_);
    return v___x_429_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_sub___redArg___boxed(
    mut v_u1_430_: *mut LeanObject,
    mut v_u2_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_432_: *mut LeanObject = core::ptr::null_mut();
    v_res_432_ = l_Std_Time_Internal_UnitVal_sub___redArg(v_u1_430_, v_u2_431_);
    lean_dec(v_u2_431_);
    lean_dec(v_u1_430_);
    return v_res_432_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_sub(
    mut v_00_u03b1_433_: *mut LeanObject,
    mut v_u1_434_: *mut LeanObject,
    mut v_u2_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_436_ = lean_int_sub(v_u1_434_, v_u2_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_sub___boxed(
    mut v_00_u03b1_437_: *mut LeanObject,
    mut v_u1_438_: *mut LeanObject,
    mut v_u2_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_440_: *mut LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Std_Time_Internal_UnitVal_sub(v_00_u03b1_437_, v_u1_438_, v_u2_439_);
    lean_dec(v_u2_439_);
    lean_dec(v_u1_438_);
    lean_dec_ref(v_00_u03b1_437_);
    return v_res_440_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_abs___redArg(
    mut v_u_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = lean_nat_abs(v_u_441_);
    v___x_443_ = lean_nat_to_int(v___x_442_);
    return v___x_443_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_abs___redArg___boxed(
    mut v_u_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_445_: *mut LeanObject = core::ptr::null_mut();
    v_res_445_ = l_Std_Time_Internal_UnitVal_abs___redArg(v_u_444_);
    lean_dec(v_u_444_);
    return v_res_445_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_abs(
    mut v_00_u03b1_446_: *mut LeanObject,
    mut v_u_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ = lean_nat_abs(v_u_447_);
    v___x_449_ = lean_nat_to_int(v___x_448_);
    return v___x_449_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_abs___boxed(
    mut v_00_u03b1_450_: *mut LeanObject,
    mut v_u_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_452_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Std_Time_Internal_UnitVal_abs(v_00_u03b1_450_, v_u_451_);
    lean_dec(v_u_451_);
    lean_dec_ref(v_00_u03b1_450_);
    return v_res_452_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_convert(
    mut v_a_453_: *mut LeanObject,
    mut v_b_454_: *mut LeanObject,
    mut v_val_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ratio_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_num_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_den_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v_ratio_456_ = l_Rat_div(v_a_453_, v_b_454_);
    v_num_457_ = lean_ctor_get(v_ratio_456_, 0);
    lean_inc(v_num_457_);
    v_den_458_ = lean_ctor_get(v_ratio_456_, 1);
    lean_inc(v_den_458_);
    lean_dec_ref(v_ratio_456_);
    v___x_459_ = lean_int_mul(v_val_455_, v_num_457_);
    lean_dec(v_num_457_);
    v___x_460_ = lean_nat_to_int(v_den_458_);
    v___x_461_ = lean_int_ediv(v___x_459_, v___x_460_);
    lean_dec(v___x_460_);
    lean_dec(v___x_459_);
    return v___x_461_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_convert___boxed(
    mut v_a_462_: *mut LeanObject,
    mut v_b_463_: *mut LeanObject,
    mut v_val_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_465_: *mut LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Std_Time_Internal_UnitVal_convert(v_a_462_, v_b_463_, v_val_464_);
    lean_dec(v_val_464_);
    lean_dec_ref(v_a_462_);
    return v_res_465_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instOfNat___redArg(
    mut v_n_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = lean_nat_to_int(v_n_466_);
    return v___x_467_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instOfNat(
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_n_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ = lean_nat_to_int(v_n_469_);
    return v___x_470_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instOfNat___boxed(
    mut v_00_u03b1_471_: *mut LeanObject,
    mut v_n_472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_473_: *mut LeanObject = core::ptr::null_mut();
    v_res_473_ = l_Std_Time_Internal_UnitVal_instOfNat(v_00_u03b1_471_, v_n_472_);
    lean_dec_ref(v_00_u03b1_471_);
    return v_res_473_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instRepr___lam__0(
    mut v_x_474_: *mut LeanObject,
    mut v_p_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: u8 = 0;
    v___x_476_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0_once),
        _init_l_Std_Time_Internal_instInhabitedUnitVal_default___closed__0,
    );
    v___x_477_ = lean_int_dec_lt(v_x_474_, v___x_476_);
    if v___x_477_ == 0 {
        let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
        v___x_478_ = l_Int_repr(v_x_474_);
        v___x_479_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_479_, 0, v___x_478_);
        return v___x_479_;
    } else {
        let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
        v___x_480_ = l_Int_repr(v_x_474_);
        v___x_481_ = lean_alloc_ctor(3, 1, (0) as u32);
        lean_ctor_set(v___x_481_, 0, v___x_480_);
        v___x_482_ = l_Repr_addAppParen(v___x_481_, v_p_475_);
        return v___x_482_;
    }
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instRepr___lam__0___boxed(
    mut v_x_483_: *mut LeanObject,
    mut v_p_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_485_: *mut LeanObject = core::ptr::null_mut();
    v_res_485_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_x_483_, v_p_484_);
    lean_dec(v_p_484_);
    lean_dec(v_x_483_);
    return v_res_485_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instRepr(
    mut v_00_u03b1_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_488_: *mut LeanObject = core::ptr::null_mut();
    v___f_488_ = l_Std_Time_Internal_UnitVal_instRepr___closed__0;
    return v___f_488_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instRepr___boxed(
    mut v_00_u03b1_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_490_: *mut LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Std_Time_Internal_UnitVal_instRepr(v_00_u03b1_489_);
    lean_dec_ref(v_00_u03b1_489_);
    return v_res_490_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instLE(
    mut v_00_u03b1_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = lean_box(0);
    return v___x_492_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instLE___boxed(
    mut v_00_u03b1_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_494_: *mut LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Std_Time_Internal_UnitVal_instLE(v_00_u03b1_493_);
    lean_dec_ref(v_00_u03b1_493_);
    return v_res_494_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instLT(
    mut v_00_u03b1_495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    v___x_496_ = lean_box(0);
    return v___x_496_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instLT___boxed(
    mut v_00_u03b1_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_498_: *mut LeanObject = core::ptr::null_mut();
    v_res_498_ = l_Std_Time_Internal_UnitVal_instLT(v_00_u03b1_497_);
    lean_dec_ref(v_00_u03b1_497_);
    return v_res_498_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instAdd(
    mut v_00_u03b1_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_500_ = lean_alloc_closure(
        l_Std_Time_Internal_UnitVal_add___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_500_, 0, v_00_u03b1_499_);
    return v___x_500_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instSub(
    mut v_00_u03b1_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_502_ = lean_alloc_closure(
        l_Std_Time_Internal_UnitVal_sub___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_502_, 0, v_00_u03b1_501_);
    return v___x_502_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instNeg(
    mut v_00_u03b1_504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_505_: *mut LeanObject = core::ptr::null_mut();
    v___f_505_ = l_Std_Time_Internal_UnitVal_instNeg___closed__0;
    return v___f_505_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instNeg___boxed(
    mut v_00_u03b1_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_507_: *mut LeanObject = core::ptr::null_mut();
    v_res_507_ = l_Std_Time_Internal_UnitVal_instNeg(v_00_u03b1_506_);
    lean_dec_ref(v_00_u03b1_506_);
    return v_res_507_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instToString(
    mut v_n_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_510_: *mut LeanObject = core::ptr::null_mut();
    v___f_510_ = l_Std_Time_Internal_UnitVal_instToString___closed__0;
    return v___f_510_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_instToString___boxed(
    mut v_n_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_512_: *mut LeanObject = core::ptr::null_mut();
    v_res_512_ = l_Std_Time_Internal_UnitVal_instToString(v_n_511_);
    lean_dec_ref(v_n_511_);
    return v_res_512_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_cast___redArg(
    mut v_x_513_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_513_);
    return v_x_513_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_cast___redArg___boxed(
    mut v_x_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_515_: *mut LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Std_Time_Internal_UnitVal_cast___redArg(v_x_514_);
    lean_dec(v_x_514_);
    return v_res_515_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_cast(
    mut v_a_516_: *mut LeanObject,
    mut v_b_517_: *mut LeanObject,
    mut v_x_518_: *mut LeanObject,
    mut v_x_519_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_519_);
    return v_x_519_;
}
pub unsafe fn l_Std_Time_Internal_UnitVal_cast___boxed(
    mut v_a_520_: *mut LeanObject,
    mut v_b_521_: *mut LeanObject,
    mut v_x_522_: *mut LeanObject,
    mut v_x_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Time_Internal_UnitVal_cast(v_a_520_, v_b_521_, v_x_522_, v_x_523_);
    lean_dec(v_x_523_);
    lean_dec_ref(v_b_521_);
    lean_dec_ref(v_a_520_);
    return v_res_524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Internal_UnitVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Internal_UnitVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Internal_UnitVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order_Ord(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Internal_UnitVal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Internal_UnitVal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Internal_UnitVal(builtin);
}
