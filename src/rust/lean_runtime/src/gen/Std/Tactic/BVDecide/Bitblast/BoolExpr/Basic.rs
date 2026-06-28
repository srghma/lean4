// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
// Imports: Init.Data.String.Basic
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Tactic_BVDecide_Gate_toString___closed__0_value: LeanStringObject<3> =
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
        m_data: [38, 38, 0],
    };
static mut l_Std_Tactic_BVDecide_Gate_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_Gate_toString___closed__0_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_Gate_toString___closed__1_value: LeanStringObject<3> =
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
        m_data: [94, 94, 0],
    };
static mut l_Std_Tactic_BVDecide_Gate_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_Gate_toString___closed__1_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_Gate_toString___closed__2_value: LeanStringObject<3> =
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
        m_data: [61, 61, 0],
    };
static mut l_Std_Tactic_BVDecide_Gate_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_Gate_toString___closed__2_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_Gate_toString___closed__3_value: LeanStringObject<3> =
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
        m_data: [124, 124, 0],
    };
static mut l_Std_Tactic_BVDecide_Gate_toString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_Gate_toString___closed__3_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [33, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [40, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [40, 105, 102, 32, 0],
    };
static mut l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorIdx(mut v_x_331_: u8) -> *mut LeanObject {
    match v_x_331_ {
        0 => {
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            v___x_332_ = lean_unsigned_to_nat(0);
            return v___x_332_;
        }
        1 => {
            let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
            v___x_333_ = lean_unsigned_to_nat(1);
            return v___x_333_;
        }
        2 => {
            let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
            v___x_334_ = lean_unsigned_to_nat(2);
            return v___x_334_;
        }
        _ => {
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            v___x_335_ = lean_unsigned_to_nat(3);
            return v___x_335_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorIdx___boxed(
    mut v_x_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_337_: u8 = 0;
    let mut v_res_338_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_337_ = (lean_unbox(v_x_336_) as u8);
    v_res_338_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_x_boxed_337_);
    return v_res_338_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_toCtorIdx(mut v_x_339_: u8) -> *mut LeanObject {
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_340_ = l_Std_Tactic_BVDecide_Gate_ctorIdx(v_x_339_);
    return v___x_340_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_toCtorIdx___boxed(
    mut v_x_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_342_: u8 = 0;
    let mut v_res_343_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_342_ = (lean_unbox(v_x_341_) as u8);
    v_res_343_ = l_Std_Tactic_BVDecide_Gate_toCtorIdx(v_x_4__boxed_342_);
    return v_res_343_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(
    mut v_k_344_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_344_);
    return v_k_344_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorElim___redArg___boxed(
    mut v_k_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ = l_Std_Tactic_BVDecide_Gate_ctorElim___redArg(v_k_345_);
    lean_dec(v_k_345_);
    return v_res_346_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorElim(
    mut v_motive_347_: *mut LeanObject,
    mut v_ctorIdx_348_: *mut LeanObject,
    mut v_t_349_: u8,
    mut v_h_350_: *mut LeanObject,
    mut v_k_351_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_351_);
    return v_k_351_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_ctorElim___boxed(
    mut v_motive_352_: *mut LeanObject,
    mut v_ctorIdx_353_: *mut LeanObject,
    mut v_t_354_: *mut LeanObject,
    mut v_h_355_: *mut LeanObject,
    mut v_k_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_357_: u8 = 0;
    let mut v_res_358_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_357_ = (lean_unbox(v_t_354_) as u8);
    v_res_358_ = l_Std_Tactic_BVDecide_Gate_ctorElim(
        v_motive_352_,
        v_ctorIdx_353_,
        v_t_boxed_357_,
        v_h_355_,
        v_k_356_,
    );
    lean_dec(v_k_356_);
    lean_dec(v_ctorIdx_353_);
    return v_res_358_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_and_elim___redArg(
    mut v_and_359_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_and_359_);
    return v_and_359_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_and_elim___redArg___boxed(
    mut v_and_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_361_: *mut LeanObject = core::ptr::null_mut();
    v_res_361_ = l_Std_Tactic_BVDecide_Gate_and_elim___redArg(v_and_360_);
    lean_dec(v_and_360_);
    return v_res_361_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_and_elim(
    mut v_motive_362_: *mut LeanObject,
    mut v_t_363_: u8,
    mut v_h_364_: *mut LeanObject,
    mut v_and_365_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_and_365_);
    return v_and_365_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_and_elim___boxed(
    mut v_motive_366_: *mut LeanObject,
    mut v_t_367_: *mut LeanObject,
    mut v_h_368_: *mut LeanObject,
    mut v_and_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_370_: u8 = 0;
    let mut v_res_371_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_370_ = (lean_unbox(v_t_367_) as u8);
    v_res_371_ =
        l_Std_Tactic_BVDecide_Gate_and_elim(v_motive_366_, v_t_boxed_370_, v_h_368_, v_and_369_);
    lean_dec(v_and_369_);
    return v_res_371_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(
    mut v_xor_372_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_xor_372_);
    return v_xor_372_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_xor_elim___redArg___boxed(
    mut v_xor_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_374_: *mut LeanObject = core::ptr::null_mut();
    v_res_374_ = l_Std_Tactic_BVDecide_Gate_xor_elim___redArg(v_xor_373_);
    lean_dec(v_xor_373_);
    return v_res_374_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_xor_elim(
    mut v_motive_375_: *mut LeanObject,
    mut v_t_376_: u8,
    mut v_h_377_: *mut LeanObject,
    mut v_xor_378_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_xor_378_);
    return v_xor_378_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_xor_elim___boxed(
    mut v_motive_379_: *mut LeanObject,
    mut v_t_380_: *mut LeanObject,
    mut v_h_381_: *mut LeanObject,
    mut v_xor_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_383_: u8 = 0;
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_383_ = (lean_unbox(v_t_380_) as u8);
    v_res_384_ =
        l_Std_Tactic_BVDecide_Gate_xor_elim(v_motive_379_, v_t_boxed_383_, v_h_381_, v_xor_382_);
    lean_dec(v_xor_382_);
    return v_res_384_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(
    mut v_beq_385_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_beq_385_);
    return v_beq_385_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_beq_elim___redArg___boxed(
    mut v_beq_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_Std_Tactic_BVDecide_Gate_beq_elim___redArg(v_beq_386_);
    lean_dec(v_beq_386_);
    return v_res_387_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_beq_elim(
    mut v_motive_388_: *mut LeanObject,
    mut v_t_389_: u8,
    mut v_h_390_: *mut LeanObject,
    mut v_beq_391_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_beq_391_);
    return v_beq_391_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_beq_elim___boxed(
    mut v_motive_392_: *mut LeanObject,
    mut v_t_393_: *mut LeanObject,
    mut v_h_394_: *mut LeanObject,
    mut v_beq_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_396_: u8 = 0;
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_396_ = (lean_unbox(v_t_393_) as u8);
    v_res_397_ =
        l_Std_Tactic_BVDecide_Gate_beq_elim(v_motive_392_, v_t_boxed_396_, v_h_394_, v_beq_395_);
    lean_dec(v_beq_395_);
    return v_res_397_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_or_elim___redArg(
    mut v_or_398_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_or_398_);
    return v_or_398_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_or_elim___redArg___boxed(
    mut v_or_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_400_: *mut LeanObject = core::ptr::null_mut();
    v_res_400_ = l_Std_Tactic_BVDecide_Gate_or_elim___redArg(v_or_399_);
    lean_dec(v_or_399_);
    return v_res_400_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_or_elim(
    mut v_motive_401_: *mut LeanObject,
    mut v_t_402_: u8,
    mut v_h_403_: *mut LeanObject,
    mut v_or_404_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_or_404_);
    return v_or_404_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_or_elim___boxed(
    mut v_motive_405_: *mut LeanObject,
    mut v_t_406_: *mut LeanObject,
    mut v_h_407_: *mut LeanObject,
    mut v_or_408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_409_: u8 = 0;
    let mut v_res_410_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_409_ = (lean_unbox(v_t_406_) as u8);
    v_res_410_ =
        l_Std_Tactic_BVDecide_Gate_or_elim(v_motive_405_, v_t_boxed_409_, v_h_407_, v_or_408_);
    lean_dec(v_or_408_);
    return v_res_410_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_toString(mut v_x_415_: u8) -> *mut LeanObject {
    match v_x_415_ {
        0 => {
            let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
            v___x_416_ = l_Std_Tactic_BVDecide_Gate_toString___closed__0;
            return v___x_416_;
        }
        1 => {
            let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
            v___x_417_ = l_Std_Tactic_BVDecide_Gate_toString___closed__1;
            return v___x_417_;
        }
        2 => {
            let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
            v___x_418_ = l_Std_Tactic_BVDecide_Gate_toString___closed__2;
            return v___x_418_;
        }
        _ => {
            let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
            v___x_419_ = l_Std_Tactic_BVDecide_Gate_toString___closed__3;
            return v___x_419_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_toString___boxed(
    mut v_x_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_40__boxed_421_: u8 = 0;
    let mut v_res_422_: *mut LeanObject = core::ptr::null_mut();
    v_x_40__boxed_421_ = (lean_unbox(v_x_420_) as u8);
    v_res_422_ = l_Std_Tactic_BVDecide_Gate_toString(v_x_40__boxed_421_);
    return v_res_422_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_eval(
    mut v_x_423_: u8,
    mut v_a_424_: u8,
    mut v_a_425_: u8,
) -> u8 {
    match v_x_423_ {
        0 => {
            if v_a_424_ == 0 {
                return v_a_424_;
            } else {
                return v_a_425_;
            }
        }
        1 => {
            if v_a_424_ == 0 {
                return v_a_425_;
            } else {
                if v_a_425_ == 0 {
                    return v_a_424_;
                } else {
                    let mut v___x_426_: u8 = 0;
                    v___x_426_ = 0;
                    return v___x_426_;
                }
            }
        }
        2 => {
            if v_a_424_ == 0 {
                if v_a_425_ == 0 {
                    let mut v___x_427_: u8 = 0;
                    v___x_427_ = 1;
                    return v___x_427_;
                } else {
                    return v_a_424_;
                }
            } else {
                return v_a_425_;
            }
        }
        _ => {
            if v_a_424_ == 0 {
                return v_a_425_;
            } else {
                return v_a_424_;
            }
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_Gate_eval___boxed(
    mut v_x_428_: *mut LeanObject,
    mut v_a_429_: *mut LeanObject,
    mut v_a_430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_237__boxed_431_: u8 = 0;
    let mut v_a_238__boxed_432_: u8 = 0;
    let mut v_a_239__boxed_433_: u8 = 0;
    let mut v_res_434_: u8 = 0;
    let mut v_r_435_: *mut LeanObject = core::ptr::null_mut();
    v_x_237__boxed_431_ = (lean_unbox(v_x_428_) as u8);
    v_a_238__boxed_432_ = (lean_unbox(v_a_429_) as u8);
    v_a_239__boxed_433_ = (lean_unbox(v_a_430_) as u8);
    v_res_434_ = l_Std_Tactic_BVDecide_Gate_eval(
        v_x_237__boxed_431_,
        v_a_238__boxed_432_,
        v_a_239__boxed_433_,
    );
    v_r_435_ = lean_box((v_res_434_) as usize);
    return v_r_435_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(
    mut v_x_436_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_436_) {
        0 => {
            let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
            v___x_437_ = lean_unsigned_to_nat(0);
            return v___x_437_;
        }
        1 => {
            let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
            v___x_438_ = lean_unsigned_to_nat(1);
            return v___x_438_;
        }
        2 => {
            let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
            v___x_439_ = lean_unsigned_to_nat(2);
            return v___x_439_;
        }
        3 => {
            let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
            v___x_440_ = lean_unsigned_to_nat(3);
            return v___x_440_;
        }
        _ => {
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            v___x_441_ = lean_unsigned_to_nat(4);
            return v___x_441_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg___boxed(
    mut v_x_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_442_);
    lean_dec_ref(v_x_442_);
    return v_res_443_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(
    mut v_00_u03b1_444_: *mut LeanObject,
    mut v_x_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v___x_446_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___redArg(v_x_445_);
    return v___x_446_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorIdx___boxed(
    mut v_00_u03b1_447_: *mut LeanObject,
    mut v_x_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Std_Tactic_BVDecide_BoolExpr_ctorIdx(v_00_u03b1_447_, v_x_448_);
    lean_dec_ref(v_x_448_);
    return v_res_449_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(
    mut v_t_450_: *mut LeanObject,
    mut v_k_451_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_450_) {
        0 => {
            let mut v_a_452_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
            v_a_452_ = lean_ctor_get(v_t_450_, 0);
            lean_inc(v_a_452_);
            lean_dec_ref_known(v_t_450_, 1);
            v___x_453_ = lean_apply_1(v_k_451_, v_a_452_);
            return v___x_453_;
        }
        1 => {
            let mut v_a_454_: u8 = 0;
            let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
            v_a_454_ = lean_ctor_get_uint8(v_t_450_, 0 as u32);
            lean_dec_ref_known(v_t_450_, 0);
            v___x_455_ = lean_box((v_a_454_) as usize);
            v___x_456_ = lean_apply_1(v_k_451_, v___x_455_);
            return v___x_456_;
        }
        2 => {
            let mut v_a_457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
            v_a_457_ = lean_ctor_get(v_t_450_, 0);
            lean_inc_ref(v_a_457_);
            lean_dec_ref_known(v_t_450_, 1);
            v___x_458_ = lean_apply_1(v_k_451_, v_a_457_);
            return v___x_458_;
        }
        3 => {
            let mut v_a_459_: u8 = 0;
            let mut v_a_460_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_461_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            v_a_459_ = lean_ctor_get_uint8(
                v_t_450_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_a_460_ = lean_ctor_get(v_t_450_, 0);
            lean_inc_ref(v_a_460_);
            v_a_461_ = lean_ctor_get(v_t_450_, 1);
            lean_inc_ref(v_a_461_);
            lean_dec_ref_known(v_t_450_, 2);
            v___x_462_ = lean_box((v_a_459_) as usize);
            v___x_463_ = lean_apply_3(v_k_451_, v___x_462_, v_a_460_, v_a_461_);
            return v___x_463_;
        }
        _ => {
            let mut v_a_464_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_465_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_466_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
            v_a_464_ = lean_ctor_get(v_t_450_, 0);
            lean_inc_ref(v_a_464_);
            v_a_465_ = lean_ctor_get(v_t_450_, 1);
            lean_inc_ref(v_a_465_);
            v_a_466_ = lean_ctor_get(v_t_450_, 2);
            lean_inc_ref(v_a_466_);
            lean_dec_ref_known(v_t_450_, 3);
            v___x_467_ = lean_apply_3(v_k_451_, v_a_464_, v_a_465_, v_a_466_);
            return v___x_467_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorElim(
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_motive_469_: *mut LeanObject,
    mut v_ctorIdx_470_: *mut LeanObject,
    mut v_t_471_: *mut LeanObject,
    mut v_h_472_: *mut LeanObject,
    mut v_k_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_471_, v_k_473_);
    return v___x_474_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ctorElim___boxed(
    mut v_00_u03b1_475_: *mut LeanObject,
    mut v_motive_476_: *mut LeanObject,
    mut v_ctorIdx_477_: *mut LeanObject,
    mut v_t_478_: *mut LeanObject,
    mut v_h_479_: *mut LeanObject,
    mut v_k_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_481_: *mut LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim(
        v_00_u03b1_475_,
        v_motive_476_,
        v_ctorIdx_477_,
        v_t_478_,
        v_h_479_,
        v_k_480_,
    );
    lean_dec(v_ctorIdx_477_);
    return v_res_481_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_literal_elim___redArg(
    mut v_t_482_: *mut LeanObject,
    mut v_literal_483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_482_, v_literal_483_);
    return v___x_484_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_literal_elim(
    mut v_00_u03b1_485_: *mut LeanObject,
    mut v_motive_486_: *mut LeanObject,
    mut v_t_487_: *mut LeanObject,
    mut v_h_488_: *mut LeanObject,
    mut v_literal_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v___x_490_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_487_, v_literal_489_);
    return v___x_490_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_const_elim___redArg(
    mut v_t_491_: *mut LeanObject,
    mut v_const_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_491_, v_const_492_);
    return v___x_493_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_const_elim(
    mut v_00_u03b1_494_: *mut LeanObject,
    mut v_motive_495_: *mut LeanObject,
    mut v_t_496_: *mut LeanObject,
    mut v_h_497_: *mut LeanObject,
    mut v_const_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_496_, v_const_498_);
    return v___x_499_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_not_elim___redArg(
    mut v_t_500_: *mut LeanObject,
    mut v_not_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_502_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_500_, v_not_501_);
    return v___x_502_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_not_elim(
    mut v_00_u03b1_503_: *mut LeanObject,
    mut v_motive_504_: *mut LeanObject,
    mut v_t_505_: *mut LeanObject,
    mut v_h_506_: *mut LeanObject,
    mut v_not_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_508_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_505_, v_not_507_);
    return v___x_508_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_gate_elim___redArg(
    mut v_t_509_: *mut LeanObject,
    mut v_gate_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_509_, v_gate_510_);
    return v___x_511_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_gate_elim(
    mut v_00_u03b1_512_: *mut LeanObject,
    mut v_motive_513_: *mut LeanObject,
    mut v_t_514_: *mut LeanObject,
    mut v_h_515_: *mut LeanObject,
    mut v_gate_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    v___x_517_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_514_, v_gate_516_);
    return v___x_517_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ite_elim___redArg(
    mut v_t_518_: *mut LeanObject,
    mut v_ite_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    v___x_520_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_518_, v_ite_519_);
    return v___x_520_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_ite_elim(
    mut v_00_u03b1_521_: *mut LeanObject,
    mut v_motive_522_: *mut LeanObject,
    mut v_t_523_: *mut LeanObject,
    mut v_h_524_: *mut LeanObject,
    mut v_ite_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = l_Std_Tactic_BVDecide_BoolExpr_ctorElim___redArg(v_t_523_, v_ite_525_);
    return v___x_526_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(
    mut v_inst_534_: *mut LeanObject,
    mut v_x_535_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_535_) {
        0 => {
            let mut v_a_536_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
            v_a_536_ = lean_ctor_get(v_x_535_, 0);
            lean_inc(v_a_536_);
            lean_dec_ref_known(v_x_535_, 1);
            v___x_537_ = lean_apply_1(v_inst_534_, v_a_536_);
            return v___x_537_;
        }
        1 => {
            let mut v_a_538_: u8 = 0;
            lean_dec_ref(v_inst_534_);
            v_a_538_ = lean_ctor_get_uint8(v_x_535_, 0 as u32);
            lean_dec_ref_known(v_x_535_, 0);
            if v_a_538_ == 0 {
                let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
                v___x_539_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__0;
                return v___x_539_;
            } else {
                let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
                v___x_540_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__1;
                return v___x_540_;
            }
        }
        2 => {
            let mut v_a_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
            v_a_541_ = lean_ctor_get(v_x_535_, 0);
            lean_inc_ref(v_a_541_);
            lean_dec_ref_known(v_x_535_, 1);
            v___x_542_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__2;
            v___x_543_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_541_);
            v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
            lean_dec_ref(v___x_543_);
            return v___x_544_;
        }
        3 => {
            let mut v_a_545_: u8 = 0;
            let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_547_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
            v_a_545_ = lean_ctor_get_uint8(
                v_x_535_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_a_546_ = lean_ctor_get(v_x_535_, 0);
            lean_inc_ref(v_a_546_);
            v_a_547_ = lean_ctor_get(v_x_535_, 1);
            lean_inc_ref(v_a_547_);
            lean_dec_ref_known(v_x_535_, 2);
            v___x_548_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__3;
            lean_inc_ref(v_inst_534_);
            v___x_549_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_546_);
            v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
            lean_dec_ref(v___x_549_);
            v___x_551_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4;
            v___x_552_ = lean_string_append(v___x_550_, v___x_551_);
            v___x_553_ = l_Std_Tactic_BVDecide_Gate_toString(v_a_545_);
            v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
            lean_dec_ref(v___x_553_);
            v___x_555_ = lean_string_append(v___x_554_, v___x_551_);
            v___x_556_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_547_);
            v___x_557_ = lean_string_append(v___x_555_, v___x_556_);
            lean_dec_ref(v___x_556_);
            v___x_558_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5;
            v___x_559_ = lean_string_append(v___x_557_, v___x_558_);
            return v___x_559_;
        }
        _ => {
            let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_561_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
            v_a_560_ = lean_ctor_get(v_x_535_, 0);
            lean_inc_ref(v_a_560_);
            v_a_561_ = lean_ctor_get(v_x_535_, 1);
            lean_inc_ref(v_a_561_);
            v_a_562_ = lean_ctor_get(v_x_535_, 2);
            lean_inc_ref(v_a_562_);
            lean_dec_ref_known(v_x_535_, 3);
            v___x_563_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__6;
            lean_inc_ref_n(v_inst_534_, 2);
            v___x_564_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_560_);
            v___x_565_ = lean_string_append(v___x_563_, v___x_564_);
            lean_dec_ref(v___x_564_);
            v___x_566_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__4;
            v___x_567_ = lean_string_append(v___x_565_, v___x_566_);
            v___x_568_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_561_);
            v___x_569_ = lean_string_append(v___x_567_, v___x_568_);
            lean_dec_ref(v___x_568_);
            v___x_570_ = lean_string_append(v___x_569_, v___x_566_);
            v___x_571_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_534_, v_a_562_);
            v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
            lean_dec_ref(v___x_571_);
            v___x_573_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg___closed__5;
            v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
            return v___x_574_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_toString(
    mut v_00_u03b1_575_: *mut LeanObject,
    mut v_inst_576_: *mut LeanObject,
    mut v_x_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = l_Std_Tactic_BVDecide_BoolExpr_toString___redArg(v_inst_576_, v_x_577_);
    return v___x_578_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_instToString___redArg(
    mut v_inst_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_BoolExpr_toString as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_580_, 0, lean_box(0));
    lean_closure_set(v___x_580_, 1, v_inst_579_);
    return v___x_580_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_instToString(
    mut v_00_u03b1_581_: *mut LeanObject,
    mut v_inst_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = lean_alloc_closure(
        l_Std_Tactic_BVDecide_BoolExpr_toString as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_583_, 0, lean_box(0));
    lean_closure_set(v___x_583_, 1, v_inst_582_);
    return v___x_583_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(
    mut v_a_584_: *mut LeanObject,
    mut v_x_585_: *mut LeanObject,
) -> u8 {
    let mut v_a_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: u8 = 0;
    let mut v_a_589_: u8 = 0;
    let mut v_a_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: u8 = 0;
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: u8 = 0;
    let mut v_a_594_: u8 = 0;
    let mut v_a_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: u8 = 0;
    let mut v___x_598_: u8 = 0;
    let mut v___x_599_: u8 = 0;
    let mut v_a_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_585_) {
                0 => {
                    v_a_586_ = lean_ctor_get(v_x_585_, 0);
                    lean_inc(v_a_586_);
                    lean_dec_ref_known(v_x_585_, 1);
                    v___x_587_ = lean_apply_1(v_a_584_, v_a_586_);
                    v___x_588_ = (lean_unbox(v___x_587_) as u8);
                    return v___x_588_;
                }
                1 => {
                    lean_dec_ref(v_a_584_);
                    v_a_589_ = lean_ctor_get_uint8(v_x_585_, 0 as u32);
                    lean_dec_ref_known(v_x_585_, 0);
                    return v_a_589_;
                }
                2 => {
                    v_a_590_ = lean_ctor_get(v_x_585_, 0);
                    lean_inc_ref(v_a_590_);
                    lean_dec_ref_known(v_x_585_, 1);
                    v___x_591_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_584_, v_a_590_);
                    if v___x_591_ == 0 {
                        v___x_592_ = 1;
                        return v___x_592_;
                    } else {
                        v___x_593_ = 0;
                        return v___x_593_;
                    }
                }
                3 => {
                    v_a_594_ = lean_ctor_get_uint8(
                        v_x_585_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_a_595_ = lean_ctor_get(v_x_585_, 0);
                    lean_inc_ref(v_a_595_);
                    v_a_596_ = lean_ctor_get(v_x_585_, 1);
                    lean_inc_ref(v_a_596_);
                    lean_dec_ref_known(v_x_585_, 2);
                    lean_inc_ref(v_a_584_);
                    v___x_597_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_584_, v_a_595_);
                    v___x_598_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_584_, v_a_596_);
                    v___x_599_ = l_Std_Tactic_BVDecide_Gate_eval(v_a_594_, v___x_597_, v___x_598_);
                    return v___x_599_;
                }
                _ => {
                    v_a_600_ = lean_ctor_get(v_x_585_, 0);
                    lean_inc_ref(v_a_600_);
                    v_a_601_ = lean_ctor_get(v_x_585_, 1);
                    lean_inc_ref(v_a_601_);
                    v_a_602_ = lean_ctor_get(v_x_585_, 2);
                    lean_inc_ref(v_a_602_);
                    lean_dec_ref_known(v_x_585_, 3);
                    lean_inc_ref(v_a_584_);
                    v___x_603_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_584_, v_a_600_);
                    if v___x_603_ == 0 {
                        lean_dec_ref(v_a_601_);
                        v_x_585_ = v_a_602_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_a_602_);
                        v_x_585_ = v_a_601_;
                        state = 0;
                        continue;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_eval___redArg___boxed(
    mut v_a_606_: *mut LeanObject,
    mut v_x_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_608_: u8 = 0;
    let mut v_r_609_: *mut LeanObject = core::ptr::null_mut();
    v_res_608_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_606_, v_x_607_);
    v_r_609_ = lean_box((v_res_608_) as usize);
    return v_r_609_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_eval(
    mut v_00_u03b1_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_x_612_: *mut LeanObject,
) -> u8 {
    let mut v___x_613_: u8 = 0;
    v___x_613_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v_a_611_, v_x_612_);
    return v___x_613_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BoolExpr_eval___boxed(
    mut v_00_u03b1_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_x_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_617_: u8 = 0;
    let mut v_r_618_: *mut LeanObject = core::ptr::null_mut();
    v_res_617_ = l_Std_Tactic_BVDecide_BoolExpr_eval(v_00_u03b1_614_, v_a_615_, v_x_616_);
    v_r_618_ = lean_box((v_res_617_) as usize);
    return v_r_618_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(
    mut v_x_619_: u8,
    mut v_h__1_620_: *mut LeanObject,
    mut v_h__2_621_: *mut LeanObject,
    mut v_h__3_622_: *mut LeanObject,
    mut v_h__4_623_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_619_ {
        0 => {
            let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_623_);
            lean_dec(v_h__3_622_);
            lean_dec(v_h__2_621_);
            v___x_624_ = lean_box(0);
            v___x_625_ = lean_apply_1(v_h__1_620_, v___x_624_);
            return v___x_625_;
        }
        1 => {
            let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_623_);
            lean_dec(v_h__3_622_);
            lean_dec(v_h__1_620_);
            v___x_626_ = lean_box(0);
            v___x_627_ = lean_apply_1(v_h__2_621_, v___x_626_);
            return v___x_627_;
        }
        2 => {
            let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_623_);
            lean_dec(v_h__2_621_);
            lean_dec(v_h__1_620_);
            v___x_628_ = lean_box(0);
            v___x_629_ = lean_apply_1(v_h__3_622_, v___x_628_);
            return v___x_629_;
        }
        _ => {
            let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_622_);
            lean_dec(v_h__2_621_);
            lean_dec(v_h__1_620_);
            v___x_630_ = lean_box(0);
            v___x_631_ = lean_apply_1(v_h__4_623_, v___x_630_);
            return v___x_631_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg___boxed(
    mut v_x_632_: *mut LeanObject,
    mut v_h__1_633_: *mut LeanObject,
    mut v_h__2_634_: *mut LeanObject,
    mut v_h__3_635_: *mut LeanObject,
    mut v_h__4_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_46__boxed_637_: u8 = 0;
    let mut v_res_638_: *mut LeanObject = core::ptr::null_mut();
    v_x_46__boxed_637_ = (lean_unbox(v_x_632_) as u8);
    v_res_638_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___redArg(v_x_46__boxed_637_, v_h__1_633_, v_h__2_634_, v_h__3_635_, v_h__4_636_);
    return v_res_638_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(
    mut v_motive_639_: *mut LeanObject,
    mut v_x_640_: u8,
    mut v_h__1_641_: *mut LeanObject,
    mut v_h__2_642_: *mut LeanObject,
    mut v_h__3_643_: *mut LeanObject,
    mut v_h__4_644_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_640_ {
        0 => {
            let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_644_);
            lean_dec(v_h__3_643_);
            lean_dec(v_h__2_642_);
            v___x_645_ = lean_box(0);
            v___x_646_ = lean_apply_1(v_h__1_641_, v___x_645_);
            return v___x_646_;
        }
        1 => {
            let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_644_);
            lean_dec(v_h__3_643_);
            lean_dec(v_h__1_641_);
            v___x_647_ = lean_box(0);
            v___x_648_ = lean_apply_1(v_h__2_642_, v___x_647_);
            return v___x_648_;
        }
        2 => {
            let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_644_);
            lean_dec(v_h__2_642_);
            lean_dec(v_h__1_641_);
            v___x_649_ = lean_box(0);
            v___x_650_ = lean_apply_1(v_h__3_643_, v___x_649_);
            return v___x_650_;
        }
        _ => {
            let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_643_);
            lean_dec(v_h__2_642_);
            lean_dec(v_h__1_641_);
            v___x_651_ = lean_box(0);
            v___x_652_ = lean_apply_1(v_h__4_644_, v___x_651_);
            return v___x_652_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter___boxed(
    mut v_motive_653_: *mut LeanObject,
    mut v_x_654_: *mut LeanObject,
    mut v_h__1_655_: *mut LeanObject,
    mut v_h__2_656_: *mut LeanObject,
    mut v_h__3_657_: *mut LeanObject,
    mut v_h__4_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_65__boxed_659_: u8 = 0;
    let mut v_res_660_: *mut LeanObject = core::ptr::null_mut();
    v_x_65__boxed_659_ = (lean_unbox(v_x_654_) as u8);
    v_res_660_ = l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic_0__Std_Tactic_BVDecide_Gate_toString_match__1_splitter(v_motive_653_, v_x_65__boxed_659_, v_h__1_655_, v_h__2_656_, v_h__3_657_, v_h__4_658_);
    return v_res_660_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
}
