// Lean compiler output
// Module: Std.Sat.AIG.RelabelNat
// Imports: Std.Sat.AIG.Relabel Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
};
use crate::r#gen::Std::Sat::AIG::Relabel::{
    initialize_Std_Sat_AIG_Relabel, l_Std_Sat_AIG_relabel___redArg,
    runtime_initialize_Std_Sat_AIG_Relabel,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Sat_AIG_RelabelNat_State_empty___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0() -> *mut LeanObject {
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_337_ = lean_box(0);
    v___x_338_ = lean_unsigned_to_nat(16);
    v___x_339_ = lean_mk_array(v___x_338_, v___x_337_);
    return v___x_339_;
}
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1() -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__0_once),
        _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__0,
    );
    v___x_341_ = lean_unsigned_to_nat(0);
    v___x_342_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_342_, 0, v___x_341_);
    lean_ctor_set(v___x_342_, 1, v___x_340_);
    return v___x_342_;
}
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2() -> *mut LeanObject {
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    v___x_343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__1),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__1_once),
        _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__1,
    );
    v___x_344_ = lean_unsigned_to_nat(0);
    v___x_345_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_345_, 0, v___x_344_);
    lean_ctor_set(v___x_345_, 1, v___x_343_);
    return v___x_345_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_empty(
    mut v_00_u03b1_346_: *mut LeanObject,
    mut v_inst_347_: *mut LeanObject,
    mut v_inst_348_: *mut LeanObject,
    mut v_decls_349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__2),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___closed__2_once),
        _init_l_Std_Sat_AIG_RelabelNat_State_empty___closed__2,
    );
    return v___x_350_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_empty___boxed(
    mut v_00_u03b1_351_: *mut LeanObject,
    mut v_inst_352_: *mut LeanObject,
    mut v_inst_353_: *mut LeanObject,
    mut v_decls_354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_355_: *mut LeanObject = core::ptr::null_mut();
    v_res_355_ = l_Std_Sat_AIG_RelabelNat_State_empty(
        v_00_u03b1_351_,
        v_inst_352_,
        v_inst_353_,
        v_decls_354_,
    );
    lean_dec_ref(v_decls_354_);
    lean_dec_ref(v_inst_353_);
    lean_dec_ref(v_inst_352_);
    return v_res_355_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(
    mut v_inst_356_: *mut LeanObject,
    mut v_inst_357_: *mut LeanObject,
    mut v_state_358_: *mut LeanObject,
    mut v_a_359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_max_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_364_: u8 = 0;
    let mut v___f_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_360_ = lean_ctor_get(v_state_358_, 0);
                v_map_361_ = lean_ctor_get(v_state_358_, 1);
                v_isSharedCheck_376_ = (!lean_is_exclusive(v_state_358_)) as u8;
                if v_isSharedCheck_376_ == 0 {
                    v___x_363_ = v_state_358_;
                    v_isShared_364_ = v_isSharedCheck_376_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_361_);
                    lean_inc(v_max_360_);
                    lean_dec(v_state_358_);
                    v___x_363_ = lean_box(0);
                    v_isShared_364_ = v_isSharedCheck_376_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_365_ = lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_365_, 0, v_inst_356_);
                lean_inc(v_a_359_);
                lean_inc_ref(v_inst_357_);
                lean_inc_ref(v___f_365_);
                v___x_366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___f_365_,
                    v_inst_357_,
                    v_map_361_,
                    v_a_359_,
                );
                if lean_obj_tag(v___x_366_) == 0 {
                    v___x_367_ = lean_unsigned_to_nat(1);
                    v___x_368_ = lean_nat_add(v_max_360_, v___x_367_);
                    v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
                        v___f_365_,
                        v_inst_357_,
                        v_map_361_,
                        v_a_359_,
                        v_max_360_,
                    );
                    if v_isShared_364_ == 0 {
                        lean_ctor_set(v___x_363_, 1, v___x_369_);
                        lean_ctor_set(v___x_363_, 0, v___x_368_);
                        v___x_371_ = v___x_363_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_368_);
                        lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
                        v___x_371_ = v_reuseFailAlloc_372_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_366_, 1);
                    lean_dec_ref(v___f_365_);
                    lean_dec(v_a_359_);
                    lean_dec_ref(v_inst_357_);
                    if v_isShared_364_ == 0 {
                        v___x_374_ = v___x_363_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_375_, 0, v_max_360_);
                        lean_ctor_set(v_reuseFailAlloc_375_, 1, v_map_361_);
                        v___x_374_ = v_reuseFailAlloc_375_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_371_;
            }
            3 => {
                return v___x_374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom(
    mut v_00_u03b1_377_: *mut LeanObject,
    mut v_inst_378_: *mut LeanObject,
    mut v_inst_379_: *mut LeanObject,
    mut v_idx_380_: *mut LeanObject,
    mut v_decls_381_: *mut LeanObject,
    mut v_hidx_382_: *mut LeanObject,
    mut v_state_383_: *mut LeanObject,
    mut v_a_384_: *mut LeanObject,
    mut v_h_385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_386_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(
        v_inst_378_,
        v_inst_379_,
        v_state_383_,
        v_a_384_,
    );
    return v___x_386_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom___boxed(
    mut v_00_u03b1_387_: *mut LeanObject,
    mut v_inst_388_: *mut LeanObject,
    mut v_inst_389_: *mut LeanObject,
    mut v_idx_390_: *mut LeanObject,
    mut v_decls_391_: *mut LeanObject,
    mut v_hidx_392_: *mut LeanObject,
    mut v_state_393_: *mut LeanObject,
    mut v_a_394_: *mut LeanObject,
    mut v_h_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_396_: *mut LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Sat_AIG_RelabelNat_State_addAtom(
        v_00_u03b1_387_,
        v_inst_388_,
        v_inst_389_,
        v_idx_390_,
        v_decls_391_,
        v_hidx_392_,
        v_state_393_,
        v_a_394_,
        v_h_395_,
    );
    lean_dec_ref(v_decls_391_);
    lean_dec(v_idx_390_);
    return v_res_396_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(
    mut v_state_397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_max_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_402_: u8 = 0;
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_398_ = lean_ctor_get(v_state_397_, 0);
                v_map_399_ = lean_ctor_get(v_state_397_, 1);
                v_isSharedCheck_406_ = (!lean_is_exclusive(v_state_397_)) as u8;
                if v_isSharedCheck_406_ == 0 {
                    v___x_401_ = v_state_397_;
                    v_isShared_402_ = v_isSharedCheck_406_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_399_);
                    lean_inc(v_max_398_);
                    lean_dec(v_state_397_);
                    v___x_401_ = lean_box(0);
                    v_isShared_402_ = v_isSharedCheck_406_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_402_ == 0 {
                    v___x_404_ = v___x_401_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_405_, 0, v_max_398_);
                    lean_ctor_set(v_reuseFailAlloc_405_, 1, v_map_399_);
                    v___x_404_ = v_reuseFailAlloc_405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse(
    mut v_00_u03b1_407_: *mut LeanObject,
    mut v_inst_408_: *mut LeanObject,
    mut v_inst_409_: *mut LeanObject,
    mut v_idx_410_: *mut LeanObject,
    mut v_decls_411_: *mut LeanObject,
    mut v_hidx_412_: *mut LeanObject,
    mut v_state_413_: *mut LeanObject,
    mut v_h_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v___x_415_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_413_);
    return v___x_415_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse___boxed(
    mut v_00_u03b1_416_: *mut LeanObject,
    mut v_inst_417_: *mut LeanObject,
    mut v_inst_418_: *mut LeanObject,
    mut v_idx_419_: *mut LeanObject,
    mut v_decls_420_: *mut LeanObject,
    mut v_hidx_421_: *mut LeanObject,
    mut v_state_422_: *mut LeanObject,
    mut v_h_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_424_: *mut LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Std_Sat_AIG_RelabelNat_State_addFalse(
        v_00_u03b1_416_,
        v_inst_417_,
        v_inst_418_,
        v_idx_419_,
        v_decls_420_,
        v_hidx_421_,
        v_state_422_,
        v_h_423_,
    );
    lean_dec_ref(v_decls_420_);
    lean_dec(v_idx_419_);
    lean_dec_ref(v_inst_418_);
    lean_dec_ref(v_inst_417_);
    return v_res_424_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(
    mut v_state_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_max_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_426_ = lean_ctor_get(v_state_425_, 0);
                v_map_427_ = lean_ctor_get(v_state_425_, 1);
                v_isSharedCheck_434_ = (!lean_is_exclusive(v_state_425_)) as u8;
                if v_isSharedCheck_434_ == 0 {
                    v___x_429_ = v_state_425_;
                    v_isShared_430_ = v_isSharedCheck_434_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_427_);
                    lean_inc(v_max_426_);
                    lean_dec(v_state_425_);
                    v___x_429_ = lean_box(0);
                    v_isShared_430_ = v_isSharedCheck_434_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_430_ == 0 {
                    v___x_432_ = v___x_429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_433_, 0, v_max_426_);
                    lean_ctor_set(v_reuseFailAlloc_433_, 1, v_map_427_);
                    v___x_432_ = v_reuseFailAlloc_433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate(
    mut v_00_u03b1_435_: *mut LeanObject,
    mut v_inst_436_: *mut LeanObject,
    mut v_inst_437_: *mut LeanObject,
    mut v_idx_438_: *mut LeanObject,
    mut v_decls_439_: *mut LeanObject,
    mut v_hidx_440_: *mut LeanObject,
    mut v_state_441_: *mut LeanObject,
    mut v_lhs_442_: *mut LeanObject,
    mut v_rhs_443_: *mut LeanObject,
    mut v_h_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_441_);
    return v___x_445_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate___boxed(
    mut v_00_u03b1_446_: *mut LeanObject,
    mut v_inst_447_: *mut LeanObject,
    mut v_inst_448_: *mut LeanObject,
    mut v_idx_449_: *mut LeanObject,
    mut v_decls_450_: *mut LeanObject,
    mut v_hidx_451_: *mut LeanObject,
    mut v_state_452_: *mut LeanObject,
    mut v_lhs_453_: *mut LeanObject,
    mut v_rhs_454_: *mut LeanObject,
    mut v_h_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Std_Sat_AIG_RelabelNat_State_addGate(
        v_00_u03b1_446_,
        v_inst_447_,
        v_inst_448_,
        v_idx_449_,
        v_decls_450_,
        v_hidx_451_,
        v_state_452_,
        v_lhs_453_,
        v_rhs_454_,
        v_h_455_,
    );
    lean_dec(v_rhs_454_);
    lean_dec(v_lhs_453_);
    lean_dec_ref(v_decls_450_);
    lean_dec(v_idx_449_);
    lean_dec_ref(v_inst_448_);
    lean_dec_ref(v_inst_447_);
    return v_res_456_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(
    mut v_inst_457_: *mut LeanObject,
    mut v_inst_458_: *mut LeanObject,
    mut v_decls_459_: *mut LeanObject,
    mut v_idx_460_: *mut LeanObject,
    mut v_state_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v_decl_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_462_ = lean_array_get_size(v_decls_459_);
                v___x_463_ = lean_nat_dec_lt(v_idx_460_, v___x_462_);
                if v___x_463_ == 0 {
                    lean_dec(v_idx_460_);
                    lean_dec_ref(v_inst_458_);
                    lean_dec_ref(v_inst_457_);
                    return v_state_461_;
                } else {
                    v_decl_464_ = lean_array_fget_borrowed(v_decls_459_, v_idx_460_);
                    match lean_obj_tag(v_decl_464_) {
                        0 => {
                            v___x_465_ = lean_unsigned_to_nat(1);
                            v___x_466_ = lean_nat_add(v_idx_460_, v___x_465_);
                            lean_dec(v_idx_460_);
                            v___x_467_ =
                                l_Std_Sat_AIG_RelabelNat_State_addFalse___redArg(v_state_461_);
                            v_idx_460_ = v___x_466_;
                            v_state_461_ = v___x_467_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_idx_469_ = lean_ctor_get(v_decl_464_, 0);
                            v___x_470_ = lean_unsigned_to_nat(1);
                            v___x_471_ = lean_nat_add(v_idx_460_, v___x_470_);
                            lean_dec(v_idx_460_);
                            lean_inc(v_idx_469_);
                            lean_inc_ref(v_inst_458_);
                            lean_inc_ref(v_inst_457_);
                            v___x_472_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___redArg(
                                v_inst_457_,
                                v_inst_458_,
                                v_state_461_,
                                v_idx_469_,
                            );
                            v_idx_460_ = v___x_471_;
                            v_state_461_ = v___x_472_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_474_ = lean_unsigned_to_nat(1);
                            v___x_475_ = lean_nat_add(v_idx_460_, v___x_474_);
                            lean_dec(v_idx_460_);
                            v___x_476_ =
                                l_Std_Sat_AIG_RelabelNat_State_addGate___redArg(v_state_461_);
                            v_idx_460_ = v___x_475_;
                            v_state_461_ = v___x_476_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg___boxed(
    mut v_inst_478_: *mut LeanObject,
    mut v_inst_479_: *mut LeanObject,
    mut v_decls_480_: *mut LeanObject,
    mut v_idx_481_: *mut LeanObject,
    mut v_state_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_483_: *mut LeanObject = core::ptr::null_mut();
    v_res_483_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(
        v_inst_478_,
        v_inst_479_,
        v_decls_480_,
        v_idx_481_,
        v_state_482_,
    );
    lean_dec_ref(v_decls_480_);
    return v_res_483_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(
    mut v_00_u03b1_484_: *mut LeanObject,
    mut v_inst_485_: *mut LeanObject,
    mut v_inst_486_: *mut LeanObject,
    mut v_decls_487_: *mut LeanObject,
    mut v_idx_488_: *mut LeanObject,
    mut v_state_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(
        v_inst_485_,
        v_inst_486_,
        v_decls_487_,
        v_idx_488_,
        v_state_489_,
    );
    return v___x_490_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___boxed(
    mut v_00_u03b1_491_: *mut LeanObject,
    mut v_inst_492_: *mut LeanObject,
    mut v_inst_493_: *mut LeanObject,
    mut v_decls_494_: *mut LeanObject,
    mut v_idx_495_: *mut LeanObject,
    mut v_state_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_497_: *mut LeanObject = core::ptr::null_mut();
    v_res_497_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go(
        v_00_u03b1_491_,
        v_inst_492_,
        v_inst_493_,
        v_decls_494_,
        v_idx_495_,
        v_state_496_,
    );
    lean_dec_ref(v_decls_494_);
    return v_res_497_;
}
pub unsafe fn l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter___redArg(
    mut v_decl_498_: *mut LeanObject,
    mut v_h__1_499_: *mut LeanObject,
    mut v_h__2_500_: *mut LeanObject,
    mut v_h__3_501_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_498_) {
        0 => {
            let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_501_);
            lean_dec(v_h__1_499_);
            v___x_502_ = lean_apply_1(v_h__2_500_, lean_box(0));
            return v___x_502_;
        }
        1 => {
            let mut v_idx_503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_501_);
            lean_dec(v_h__2_500_);
            v_idx_503_ = lean_ctor_get(v_decl_498_, 0);
            lean_inc(v_idx_503_);
            lean_dec_ref_known(v_decl_498_, 1);
            v___x_504_ = lean_apply_2(v_h__1_499_, v_idx_503_, lean_box(0));
            return v___x_504_;
        }
        _ => {
            let mut v_l_505_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_506_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_500_);
            lean_dec(v_h__1_499_);
            v_l_505_ = lean_ctor_get(v_decl_498_, 0);
            lean_inc(v_l_505_);
            v_r_506_ = lean_ctor_get(v_decl_498_, 1);
            lean_inc(v_r_506_);
            lean_dec_ref_known(v_decl_498_, 2);
            v___x_507_ = lean_apply_3(v_h__3_501_, v_l_505_, v_r_506_, lean_box(0));
            return v___x_507_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_RelabelNat_State_ofAIGAux_go_match__1_splitter(
    mut v_00_u03b1_508_: *mut LeanObject,
    mut v_motive_509_: *mut LeanObject,
    mut v_decl_510_: *mut LeanObject,
    mut v_h__1_511_: *mut LeanObject,
    mut v_h__2_512_: *mut LeanObject,
    mut v_h__3_513_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_decl_510_) {
        0 => {
            let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_513_);
            lean_dec(v_h__1_511_);
            v___x_514_ = lean_apply_1(v_h__2_512_, lean_box(0));
            return v___x_514_;
        }
        1 => {
            let mut v_idx_515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_513_);
            lean_dec(v_h__2_512_);
            v_idx_515_ = lean_ctor_get(v_decl_510_, 0);
            lean_inc(v_idx_515_);
            lean_dec_ref_known(v_decl_510_, 1);
            v___x_516_ = lean_apply_2(v_h__1_511_, v_idx_515_, lean_box(0));
            return v___x_516_;
        }
        _ => {
            let mut v_l_517_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_512_);
            lean_dec(v_h__1_511_);
            v_l_517_ = lean_ctor_get(v_decl_510_, 0);
            lean_inc(v_l_517_);
            v_r_518_ = lean_ctor_get(v_decl_510_, 1);
            lean_inc(v_r_518_);
            lean_dec_ref_known(v_decl_510_, 2);
            v___x_519_ = lean_apply_3(v_h__3_513_, v_l_517_, v_r_518_, lean_box(0));
            return v___x_519_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(
    mut v_inst_520_: *mut LeanObject,
    mut v_inst_521_: *mut LeanObject,
    mut v_aig_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v_decls_523_ = lean_ctor_get(v_aig_522_, 0);
    v___x_524_ = lean_unsigned_to_nat(0);
    v___x_525_ =
        l_Std_Sat_AIG_RelabelNat_State_empty(lean_box(0), v_inst_520_, v_inst_521_, v_decls_523_);
    v___x_526_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___redArg(
        v_inst_520_,
        v_inst_521_,
        v_decls_523_,
        v___x_524_,
        v___x_525_,
    );
    return v___x_526_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg___boxed(
    mut v_inst_527_: *mut LeanObject,
    mut v_inst_528_: *mut LeanObject,
    mut v_aig_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_530_: *mut LeanObject = core::ptr::null_mut();
    v_res_530_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_527_, v_inst_528_, v_aig_529_);
    lean_dec_ref(v_aig_529_);
    return v_res_530_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(
    mut v_00_u03b1_531_: *mut LeanObject,
    mut v_inst_532_: *mut LeanObject,
    mut v_inst_533_: *mut LeanObject,
    mut v_aig_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_532_, v_inst_533_, v_aig_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___boxed(
    mut v_00_u03b1_536_: *mut LeanObject,
    mut v_inst_537_: *mut LeanObject,
    mut v_inst_538_: *mut LeanObject,
    mut v_aig_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux(
        v_00_u03b1_536_,
        v_inst_537_,
        v_inst_538_,
        v_aig_539_,
    );
    lean_dec_ref(v_aig_539_);
    return v_res_540_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_aig_543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_544_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___redArg(v_inst_541_, v_inst_542_, v_aig_543_);
    v_map_545_ = lean_ctor_get(v___x_544_, 1);
    lean_inc_ref(v_map_545_);
    lean_dec_ref(v___x_544_);
    return v_map_545_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg___boxed(
    mut v_inst_546_: *mut LeanObject,
    mut v_inst_547_: *mut LeanObject,
    mut v_aig_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_549_: *mut LeanObject = core::ptr::null_mut();
    v_res_549_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_546_, v_inst_547_, v_aig_548_);
    lean_dec_ref(v_aig_548_);
    return v_res_549_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG(
    mut v_00_u03b1_550_: *mut LeanObject,
    mut v_inst_551_: *mut LeanObject,
    mut v_inst_552_: *mut LeanObject,
    mut v_aig_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    v___x_554_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_551_, v_inst_552_, v_aig_553_);
    return v___x_554_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG___boxed(
    mut v_00_u03b1_555_: *mut LeanObject,
    mut v_inst_556_: *mut LeanObject,
    mut v_inst_557_: *mut LeanObject,
    mut v_aig_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_559_: *mut LeanObject = core::ptr::null_mut();
    v_res_559_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIG(v_00_u03b1_555_, v_inst_556_, v_inst_557_, v_aig_558_);
    lean_dec_ref(v_aig_558_);
    return v_res_559_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(
    mut v___f_560_: *mut LeanObject,
    mut v_inst_561_: *mut LeanObject,
    mut v_map_562_: *mut LeanObject,
    mut v_x_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_560_,
        v_inst_561_,
        v_map_562_,
        v_x_563_,
    );
    if lean_obj_tag(v___x_564_) == 0 {
        let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
        v___x_565_ = lean_unsigned_to_nat(0);
        return v___x_565_;
    } else {
        let mut v_val_566_: *mut LeanObject = core::ptr::null_mut();
        v_val_566_ = lean_ctor_get(v___x_564_, 0);
        lean_inc(v_val_566_);
        lean_dec_ref_known(v___x_564_, 1);
        return v_val_566_;
    }
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed(
    mut v___f_567_: *mut LeanObject,
    mut v_inst_568_: *mut LeanObject,
    mut v_map_569_: *mut LeanObject,
    mut v_x_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_571_: *mut LeanObject = core::ptr::null_mut();
    v_res_571_ = l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0(
        v___f_567_,
        v_inst_568_,
        v_map_569_,
        v_x_570_,
    );
    lean_dec_ref(v_map_569_);
    return v_res_571_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___redArg(
    mut v_inst_572_: *mut LeanObject,
    mut v_inst_573_: *mut LeanObject,
    mut v_aig_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_573_);
    lean_inc_ref(v_inst_572_);
    v_map_575_ =
        l_Std_Sat_AIG_RelabelNat_State_ofAIG___redArg(v_inst_572_, v_inst_573_, v_aig_574_);
    v___f_576_ = lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_576_, 0, v_inst_572_);
    lean_inc_ref(v_map_575_);
    v___f_577_ = lean_alloc_closure(
        l_Std_Sat_AIG_relabelNat_x27___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_577_, 0, v___f_576_);
    lean_closure_set(v___f_577_, 1, v_inst_573_);
    lean_closure_set(v___f_577_, 2, v_map_575_);
    v_aig_578_ = l_Std_Sat_AIG_relabel___redArg(v___f_577_, v_aig_574_);
    v___x_579_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_579_, 0, v_aig_578_);
    lean_ctor_set(v___x_579_, 1, v_map_575_);
    return v___x_579_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27(
    mut v_00_u03b1_580_: *mut LeanObject,
    mut v_inst_581_: *mut LeanObject,
    mut v_inst_582_: *mut LeanObject,
    mut v_aig_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_581_, v_inst_582_, v_aig_583_);
    return v___x_584_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat___redArg(
    mut v_inst_585_: *mut LeanObject,
    mut v_inst_586_: *mut LeanObject,
    mut v_aig_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_588_ = l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_585_, v_inst_586_, v_aig_587_);
    v_fst_589_ = lean_ctor_get(v___x_588_, 0);
    lean_inc(v_fst_589_);
    lean_dec_ref(v___x_588_);
    return v_fst_589_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat(
    mut v_00_u03b1_590_: *mut LeanObject,
    mut v_inst_591_: *mut LeanObject,
    mut v_inst_592_: *mut LeanObject,
    mut v_aig_593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    v___x_594_ = l_Std_Sat_AIG_relabelNat___redArg(v_inst_591_, v_inst_592_, v_aig_593_);
    return v___x_594_;
}
pub unsafe fn l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter___redArg(
    mut v_x_595_: *mut LeanObject,
    mut v_h__1_596_: *mut LeanObject,
    mut v_h__2_597_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_595_) == 0 {
        let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_596_);
        v___x_598_ = lean_box(0);
        v___x_599_ = lean_apply_1(v_h__2_597_, v___x_598_);
        return v___x_599_;
    } else {
        let mut v_val_600_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_597_);
        v_val_600_ = lean_ctor_get(v_x_595_, 0);
        lean_inc(v_val_600_);
        lean_dec_ref_known(v_x_595_, 1);
        v___x_601_ = lean_apply_1(v_h__1_596_, v_val_600_);
        return v___x_601_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_RelabelNat_0__Std_Sat_AIG_relabelNat_x27_match__1_splitter(
    mut v_motive_602_: *mut LeanObject,
    mut v_x_603_: *mut LeanObject,
    mut v_h__1_604_: *mut LeanObject,
    mut v_h__2_605_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_603_) == 0 {
        let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_604_);
        v___x_606_ = lean_box(0);
        v___x_607_ = lean_apply_1(v_h__2_605_, v___x_606_);
        return v___x_607_;
    } else {
        let mut v_val_608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_605_);
        v_val_608_ = lean_ctor_get(v_x_603_, 0);
        lean_inc(v_val_608_);
        lean_dec_ref_known(v_x_603_, 1);
        v___x_609_ = lean_apply_1(v_h__1_604_, v_val_608_);
        return v___x_609_;
    }
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(
    mut v_inst_610_: *mut LeanObject,
    mut v_inst_611_: *mut LeanObject,
    mut v_entry_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_aig_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v_res_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v_gate_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_625_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_628_: u8 = 0;
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut v_isSharedCheck_639_: u8 = 0;
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aig_613_ = lean_ctor_get(v_entry_612_, 0);
                v_ref_614_ = lean_ctor_get(v_entry_612_, 1);
                v_isSharedCheck_640_ = (!lean_is_exclusive(v_entry_612_)) as u8;
                if v_isSharedCheck_640_ == 0 {
                    v___x_616_ = v_entry_612_;
                    v_isShared_617_ = v_isSharedCheck_640_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_614_);
                    lean_inc(v_aig_613_);
                    lean_dec(v_entry_612_);
                    v___x_616_ = lean_box(0);
                    v_isShared_617_ = v_isSharedCheck_640_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_res_618_ =
                    l_Std_Sat_AIG_relabelNat_x27___redArg(v_inst_610_, v_inst_611_, v_aig_613_);
                v_fst_619_ = lean_ctor_get(v_res_618_, 0);
                v_snd_620_ = lean_ctor_get(v_res_618_, 1);
                v_isSharedCheck_639_ = (!lean_is_exclusive(v_res_618_)) as u8;
                if v_isSharedCheck_639_ == 0 {
                    v___x_622_ = v_res_618_;
                    v_isShared_623_ = v_isSharedCheck_639_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_620_);
                    lean_inc(v_fst_619_);
                    lean_dec(v_res_618_);
                    v___x_622_ = lean_box(0);
                    v_isShared_623_ = v_isSharedCheck_639_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_624_ = lean_ctor_get(v_ref_614_, 0);
                v_invert_625_ = lean_ctor_get_uint8(
                    v_ref_614_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_638_ = (!lean_is_exclusive(v_ref_614_)) as u8;
                if v_isSharedCheck_638_ == 0 {
                    v___x_627_ = v_ref_614_;
                    v_isShared_628_ = v_isSharedCheck_638_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_gate_624_);
                    lean_dec(v_ref_614_);
                    v___x_627_ = lean_box(0);
                    v_isShared_628_ = v_isSharedCheck_638_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_628_ == 0 {
                    v___x_630_ = v___x_627_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_637_, 0, v_gate_624_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_637_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_625_,
                    );
                    v___x_630_ = v_reuseFailAlloc_637_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_617_ == 0 {
                    lean_ctor_set(v___x_616_, 1, v___x_630_);
                    lean_ctor_set(v___x_616_, 0, v_fst_619_);
                    v_entry_632_ = v___x_616_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_636_, 0, v_fst_619_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_630_);
                    v_entry_632_ = v_reuseFailAlloc_636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_623_ == 0 {
                    lean_ctor_set(v___x_622_, 0, v_entry_632_);
                    v___x_634_ = v___x_622_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_635_, 0, v_entry_632_);
                    lean_ctor_set(v_reuseFailAlloc_635_, 1, v_snd_620_);
                    v___x_634_ = v_reuseFailAlloc_635_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabelNat_x27(
    mut v_00_u03b1_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
    mut v_entry_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    v___x_645_ =
        l_Std_Sat_AIG_Entrypoint_relabelNat_x27___redArg(v_inst_642_, v_inst_643_, v_entry_644_);
    return v___x_645_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(
    mut v_inst_646_: *mut LeanObject,
    mut v_inst_647_: *mut LeanObject,
    mut v_entry_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_653_: u8 = 0;
    let mut v_gate_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_655_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_666_: u8 = 0;
    let mut v_isSharedCheck_667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_649_ = lean_ctor_get(v_entry_648_, 1);
                v_aig_650_ = lean_ctor_get(v_entry_648_, 0);
                v_isSharedCheck_667_ = (!lean_is_exclusive(v_entry_648_)) as u8;
                if v_isSharedCheck_667_ == 0 {
                    v___x_652_ = v_entry_648_;
                    v_isShared_653_ = v_isSharedCheck_667_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_649_);
                    lean_inc(v_aig_650_);
                    lean_dec(v_entry_648_);
                    v___x_652_ = lean_box(0);
                    v_isShared_653_ = v_isSharedCheck_667_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_654_ = lean_ctor_get(v_ref_649_, 0);
                v_invert_655_ = lean_ctor_get_uint8(
                    v_ref_649_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_666_ = (!lean_is_exclusive(v_ref_649_)) as u8;
                if v_isSharedCheck_666_ == 0 {
                    v___x_657_ = v_ref_649_;
                    v_isShared_658_ = v_isSharedCheck_666_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_gate_654_);
                    lean_dec(v_ref_649_);
                    v___x_657_ = lean_box(0);
                    v_isShared_658_ = v_isSharedCheck_666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_659_ =
                    l_Std_Sat_AIG_relabelNat___redArg(v_inst_646_, v_inst_647_, v_aig_650_);
                if v_isShared_658_ == 0 {
                    v___x_661_ = v___x_657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_665_, 0, v_gate_654_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_665_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_655_,
                    );
                    v___x_661_ = v_reuseFailAlloc_665_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_653_ == 0 {
                    lean_ctor_set(v___x_652_, 1, v___x_661_);
                    lean_ctor_set(v___x_652_, 0, v___x_659_);
                    v___x_663_ = v___x_652_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_659_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
                    v___x_663_ = v_reuseFailAlloc_664_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabelNat(
    mut v_00_u03b1_668_: *mut LeanObject,
    mut v_inst_669_: *mut LeanObject,
    mut v_inst_670_: *mut LeanObject,
    mut v_entry_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v___x_672_ =
        l_Std_Sat_AIG_Entrypoint_relabelNat___redArg(v_inst_669_, v_inst_670_, v_entry_671_);
    return v___x_672_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_RelabelNat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Relabel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_RelabelNat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_RelabelNat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Relabel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RelabelNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_RelabelNat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_RelabelNat(builtin);
}
