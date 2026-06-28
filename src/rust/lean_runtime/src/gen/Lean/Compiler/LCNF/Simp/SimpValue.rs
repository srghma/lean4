// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpValue
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Lean::Compiler::ImplementedByAttr::l_Lean_Compiler_getImplementedBy_x3f;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Arg_toLetValue___redArg, l_Lean_Compiler_LCNF_LetValue_toExpr,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Simp::DiscrM::{
    l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg,
    l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(
    mut v_e_373_: *mut LeanObject,
    mut v_a_374_: *mut LeanObject,
    mut v_a_375_: *mut LeanObject,
    mut v_a_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_idx_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_384_: u8 = 0;
    let mut v_val_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v_val_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_411_: u8 = 0;
    let mut v_a_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_373_) == 2 {
                    v_idx_378_ = lean_ctor_get(v_e_373_, 1);
                    v_struct_379_ = lean_ctor_get(v_e_373_, 2);
                    v___x_380_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                        v_struct_379_,
                        v_a_374_,
                        v_a_375_,
                        v_a_376_,
                    );
                    if lean_obj_tag(v___x_380_) == 0 {
                        v_a_381_ = lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_411_ = (!lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_411_ == 0 {
                            v___x_383_ = v___x_380_;
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_381_);
                            lean_dec(v___x_380_);
                            v___x_383_ = lean_box(0);
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_412_ = lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_419_ = (!lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_419_ == 0 {
                            v___x_414_ = v___x_380_;
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_412_);
                            lean_dec(v___x_380_);
                            v___x_414_ = lean_box(0);
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_420_ = lean_box(0);
                    v___x_421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_421_, 0, v___x_420_);
                    return v___x_421_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_381_) == 1 {
                    v_val_385_ = lean_ctor_get(v_a_381_, 0);
                    v_isSharedCheck_406_ = (!lean_is_exclusive(v_a_381_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v___x_387_ = v_a_381_;
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_385_);
                        lean_dec(v_a_381_);
                        v___x_387_ = lean_box(0);
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_381_);
                    v___x_407_ = lean_box(0);
                    if v_isShared_384_ == 0 {
                        lean_ctor_set(v___x_383_, 0, v___x_407_);
                        v___x_409_ = v___x_383_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
                        v___x_409_ = v_reuseFailAlloc_410_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_val_385_) == 0 {
                    v_val_389_ = lean_ctor_get(v_val_385_, 0);
                    lean_inc_ref(v_val_389_);
                    v_args_390_ = lean_ctor_get(v_val_385_, 1);
                    lean_inc_ref(v_args_390_);
                    lean_dec_ref_known(v_val_385_, 2);
                    v_numParams_391_ = lean_ctor_get(v_val_389_, 3);
                    lean_inc(v_numParams_391_);
                    lean_dec_ref(v_val_389_);
                    v___x_392_ = lean_box(0);
                    v___x_393_ = lean_nat_add(v_numParams_391_, v_idx_378_);
                    lean_dec(v_numParams_391_);
                    v___x_394_ = lean_array_get(v___x_392_, v_args_390_, v___x_393_);
                    lean_dec(v___x_393_);
                    lean_dec_ref(v_args_390_);
                    v___x_395_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_394_);
                    lean_dec(v___x_394_);
                    if v_isShared_388_ == 0 {
                        lean_ctor_set(v___x_387_, 0, v___x_395_);
                        v___x_397_ = v___x_387_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_395_);
                        v___x_397_ = v_reuseFailAlloc_401_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_val_385_, 1);
                    lean_del_object(v___x_387_);
                    v___x_402_ = lean_box(0);
                    if v_isShared_384_ == 0 {
                        lean_ctor_set(v___x_383_, 0, v___x_402_);
                        v___x_404_ = v___x_383_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
                        v___x_404_ = v_reuseFailAlloc_405_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_384_ == 0 {
                    lean_ctor_set(v___x_383_, 0, v___x_397_);
                    v___x_399_ = v___x_383_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
                    v___x_399_ = v_reuseFailAlloc_400_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_399_;
            }
            5 => {
                return v___x_404_;
            }
            6 => {
                return v___x_409_;
            }
            7 => {
                if v_isShared_415_ == 0 {
                    v___x_417_ = v___x_414_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
                    v___x_417_ = v_reuseFailAlloc_418_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg___boxed(
    mut v_e_422_: *mut LeanObject,
    mut v_a_423_: *mut LeanObject,
    mut v_a_424_: *mut LeanObject,
    mut v_a_425_: *mut LeanObject,
    mut v_a_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_427_: *mut LeanObject = core::ptr::null_mut();
    v_res_427_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_422_, v_a_423_, v_a_424_, v_a_425_);
    lean_dec(v_a_425_);
    lean_dec(v_a_424_);
    lean_dec_ref(v_a_423_);
    lean_dec(v_e_422_);
    return v_res_427_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
    mut v_e_428_: *mut LeanObject,
    mut v_a_429_: *mut LeanObject,
    mut v_a_430_: *mut LeanObject,
    mut v_a_431_: *mut LeanObject,
    mut v_a_432_: *mut LeanObject,
    mut v_a_433_: *mut LeanObject,
    mut v_a_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    v___x_437_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_428_, v_a_431_, v_a_433_, v_a_435_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(
    mut v_e_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
    mut v_a_440_: *mut LeanObject,
    mut v_a_441_: *mut LeanObject,
    mut v_a_442_: *mut LeanObject,
    mut v_a_443_: *mut LeanObject,
    mut v_a_444_: *mut LeanObject,
    mut v_a_445_: *mut LeanObject,
    mut v_a_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
        v_e_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
    );
    lean_dec(v_a_445_);
    lean_dec_ref(v_a_444_);
    lean_dec(v_a_443_);
    lean_dec_ref(v_a_442_);
    lean_dec_ref(v_a_441_);
    lean_dec(v_a_440_);
    lean_dec_ref(v_a_439_);
    lean_dec(v_e_438_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(
    mut v_e_450_: *mut LeanObject,
    mut v_a_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v_val_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v_value_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_475_: u8 = 0;
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_493_: u8 = 0;
    let mut v_fvarId_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v_a_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_450_) == 4 {
                    v_fvarId_453_ = lean_ctor_get(v_e_450_, 0);
                    v_args_454_ = lean_ctor_get(v_e_450_, 1);
                    v___x_455_ = 0;
                    v___x_456_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                        v___x_455_,
                        v_fvarId_453_,
                        v_a_451_,
                    );
                    if lean_obj_tag(v___x_456_) == 0 {
                        v_a_457_ = lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_526_ = (!lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_526_ == 0 {
                            v___x_459_ = v___x_456_;
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_457_);
                            lean_dec(v___x_456_);
                            v___x_459_ = lean_box(0);
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_527_ = lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_534_ = (!lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_534_ == 0 {
                            v___x_529_ = v___x_456_;
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_527_);
                            lean_dec(v___x_456_);
                            v___x_529_ = lean_box(0);
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    v___x_535_ = lean_box(0);
                    v___x_536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_457_) == 1 {
                    v_val_461_ = lean_ctor_get(v_a_457_, 0);
                    v_isSharedCheck_521_ = (!lean_is_exclusive(v_a_457_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_463_ = v_a_457_;
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_461_);
                        lean_dec(v_a_457_);
                        v___x_463_ = lean_box(0);
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_457_);
                    v___x_522_ = lean_box(0);
                    if v_isShared_460_ == 0 {
                        lean_ctor_set(v___x_459_, 0, v___x_522_);
                        v___x_524_ = v___x_459_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
                        v___x_524_ = v_reuseFailAlloc_525_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_value_465_ = lean_ctor_get(v_val_461_, 3);
                lean_inc(v_value_465_);
                lean_dec(v_val_461_);
                match lean_obj_tag(v_value_465_) {
                    1 => {
                        lean_del_object(v___x_463_);
                        v___x_466_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0;
                        if v_isShared_460_ == 0 {
                            lean_ctor_set(v___x_459_, 0, v___x_466_);
                            v___x_468_ = v___x_459_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
                            v___x_468_ = v_reuseFailAlloc_469_;
                            state = 3;
                            continue;
                        }
                    }
                    3 => {
                        v_declName_470_ = lean_ctor_get(v_value_465_, 0);
                        v_us_471_ = lean_ctor_get(v_value_465_, 1);
                        v_args_472_ = lean_ctor_get(v_value_465_, 2);
                        v_isSharedCheck_493_ = (!lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_493_ == 0 {
                            v___x_474_ = v_value_465_;
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_args_472_);
                            lean_inc(v_us_471_);
                            lean_inc(v_declName_470_);
                            lean_dec(v_value_465_);
                            v___x_474_ = lean_box(0);
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        }
                    }
                    4 => {
                        v_fvarId_494_ = lean_ctor_get(v_value_465_, 0);
                        v_args_495_ = lean_ctor_get(v_value_465_, 1);
                        v_isSharedCheck_516_ = (!lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_516_ == 0 {
                            v___x_497_ = v_value_465_;
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_args_495_);
                            lean_inc(v_fvarId_494_);
                            lean_dec(v_value_465_);
                            v___x_497_ = lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_value_465_);
                        lean_del_object(v___x_463_);
                        v___x_517_ = lean_box(0);
                        if v_isShared_460_ == 0 {
                            lean_ctor_set(v___x_459_, 0, v___x_517_);
                            v___x_519_ = v___x_459_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
                            v___x_519_ = v_reuseFailAlloc_520_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_468_;
            }
            4 => {
                v___x_476_ = lean_array_get_size(v_args_454_);
                v___x_477_ = lean_unsigned_to_nat(0);
                v___x_478_ = lean_nat_dec_eq(v___x_476_, v___x_477_);
                if v___x_478_ == 0 {
                    v___x_479_ = l_Array_append___redArg(v_args_472_, v_args_454_);
                    if v_isShared_475_ == 0 {
                        lean_ctor_set(v___x_474_, 2, v___x_479_);
                        v___x_481_ = v___x_474_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_488_ = lean_alloc_ctor(3, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_488_, 0, v_declName_470_);
                        lean_ctor_set(v_reuseFailAlloc_488_, 1, v_us_471_);
                        lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_479_);
                        v___x_481_ = v_reuseFailAlloc_488_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_474_);
                    lean_dec_ref(v_args_472_);
                    lean_dec(v_us_471_);
                    lean_dec(v_declName_470_);
                    lean_del_object(v___x_463_);
                    v___x_489_ = lean_box(0);
                    if v_isShared_460_ == 0 {
                        lean_ctor_set(v___x_459_, 0, v___x_489_);
                        v___x_491_ = v___x_459_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
                        v___x_491_ = v_reuseFailAlloc_492_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_464_ == 0 {
                    lean_ctor_set(v___x_463_, 0, v___x_481_);
                    v___x_483_ = v___x_463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
                    v___x_483_ = v_reuseFailAlloc_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_460_ == 0 {
                    lean_ctor_set(v___x_459_, 0, v___x_483_);
                    v___x_485_ = v___x_459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
                    v___x_485_ = v_reuseFailAlloc_486_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_485_;
            }
            8 => {
                return v___x_491_;
            }
            9 => {
                v___x_499_ = lean_array_get_size(v_args_454_);
                v___x_500_ = lean_unsigned_to_nat(0);
                v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
                if v___x_501_ == 0 {
                    v___x_502_ = l_Array_append___redArg(v_args_495_, v_args_454_);
                    if v_isShared_498_ == 0 {
                        lean_ctor_set(v___x_497_, 1, v___x_502_);
                        v___x_504_ = v___x_497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_511_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fvarId_494_);
                        lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_502_);
                        v___x_504_ = v_reuseFailAlloc_511_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_497_);
                    lean_dec_ref(v_args_495_);
                    lean_dec(v_fvarId_494_);
                    lean_del_object(v___x_463_);
                    v___x_512_ = lean_box(0);
                    if v_isShared_460_ == 0 {
                        lean_ctor_set(v___x_459_, 0, v___x_512_);
                        v___x_514_ = v___x_459_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                        v___x_514_ = v_reuseFailAlloc_515_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_464_ == 0 {
                    lean_ctor_set(v___x_463_, 0, v___x_504_);
                    v___x_506_ = v___x_463_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
                    v___x_506_ = v_reuseFailAlloc_510_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_460_ == 0 {
                    lean_ctor_set(v___x_459_, 0, v___x_506_);
                    v___x_508_ = v___x_459_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
                    v___x_508_ = v_reuseFailAlloc_509_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_508_;
            }
            13 => {
                return v___x_514_;
            }
            14 => {
                return v___x_519_;
            }
            15 => {
                return v___x_524_;
            }
            16 => {
                if v_isShared_530_ == 0 {
                    v___x_532_ = v___x_529_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
                    v___x_532_ = v_reuseFailAlloc_533_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___boxed(
    mut v_e_537_: *mut LeanObject,
    mut v_a_538_: *mut LeanObject,
    mut v_a_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_537_, v_a_538_);
    lean_dec(v_a_538_);
    lean_dec(v_e_537_);
    return v_res_540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
    mut v_e_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
    mut v_a_543_: *mut LeanObject,
    mut v_a_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
    mut v_a_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_541_, v_a_546_);
    return v___x_550_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(
    mut v_e_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
    mut v_a_554_: *mut LeanObject,
    mut v_a_555_: *mut LeanObject,
    mut v_a_556_: *mut LeanObject,
    mut v_a_557_: *mut LeanObject,
    mut v_a_558_: *mut LeanObject,
    mut v_a_559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
        v_e_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_,
    );
    lean_dec(v_a_558_);
    lean_dec_ref(v_a_557_);
    lean_dec(v_a_556_);
    lean_dec_ref(v_a_555_);
    lean_dec_ref(v_a_554_);
    lean_dec(v_a_553_);
    lean_dec_ref(v_a_552_);
    lean_dec(v_e_551_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
    mut v_e_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
    mut v_a_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
    mut v_a_567_: *mut LeanObject,
    mut v_a_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v_val_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_563_) == 3 {
                    v_declName_573_ = lean_ctor_get(v_e_563_, 0);
                    v___x_574_ = lean_st_ref_get(v_a_568_);
                    v_env_575_ = lean_ctor_get(v___x_574_, 0);
                    lean_inc_ref(v_env_575_);
                    lean_dec(v___x_574_);
                    v___x_576_ = 0;
                    lean_inc(v_declName_573_);
                    v___x_577_ =
                        l_Lean_Environment_find_x3f(v_env_575_, v_declName_573_, v___x_576_);
                    if lean_obj_tag(v___x_577_) == 1 {
                        v_val_578_ = lean_ctor_get(v___x_577_, 0);
                        lean_inc(v_val_578_);
                        lean_dec_ref_known(v___x_577_, 1);
                        if lean_obj_tag(v_val_578_) == 6 {
                            lean_dec_ref_known(v_val_578_, 1);
                            v___x_579_ = 0;
                            v___x_580_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_579_, v_e_563_);
                            v___x_581_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
                                v___x_580_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_,
                            );
                            if lean_obj_tag(v___x_581_) == 0 {
                                v_a_582_ = lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_603_ = (!lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_603_ == 0 {
                                    v___x_584_ = v___x_581_;
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_582_);
                                    lean_dec(v___x_581_);
                                    v___x_584_ = lean_box(0);
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_604_ = lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_611_ = (!lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_611_ == 0 {
                                    v___x_606_ = v___x_581_;
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_604_);
                                    lean_dec(v___x_581_);
                                    v___x_606_ = lean_box(0);
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_578_);
                            lean_dec_ref_known(v_e_563_, 3);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_577_);
                        lean_dec_ref_known(v_e_563_, 3);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_e_563_);
                    v___x_612_ = lean_box(0);
                    v___x_613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_613_, 0, v___x_612_);
                    return v___x_613_;
                }
            }
            1 => {
                v___x_571_ = lean_box(0);
                v___x_572_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_572_, 0, v___x_571_);
                return v___x_572_;
            }
            2 => {
                if lean_obj_tag(v_a_582_) == 1 {
                    v_val_586_ = lean_ctor_get(v_a_582_, 0);
                    v_isSharedCheck_598_ = (!lean_is_exclusive(v_a_582_)) as u8;
                    if v_isSharedCheck_598_ == 0 {
                        v___x_588_ = v_a_582_;
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_586_);
                        lean_dec(v_a_582_);
                        v___x_588_ = lean_box(0);
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_582_);
                    v___x_599_ = lean_box(0);
                    if v_isShared_585_ == 0 {
                        lean_ctor_set(v___x_584_, 0, v___x_599_);
                        v___x_601_ = v___x_584_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
                        v___x_601_ = v_reuseFailAlloc_602_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_590_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0;
                v___x_591_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_591_, 0, v_val_586_);
                lean_ctor_set(v___x_591_, 1, v___x_590_);
                if v_isShared_589_ == 0 {
                    lean_ctor_set(v___x_588_, 0, v___x_591_);
                    v___x_593_ = v___x_588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
                    v___x_593_ = v_reuseFailAlloc_597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_585_ == 0 {
                    lean_ctor_set(v___x_584_, 0, v___x_593_);
                    v___x_595_ = v___x_584_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
                    v___x_595_ = v_reuseFailAlloc_596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_595_;
            }
            6 => {
                return v___x_601_;
            }
            7 => {
                if v_isShared_607_ == 0 {
                    v___x_609_ = v___x_606_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
                    v___x_609_ = v_reuseFailAlloc_610_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___boxed(
    mut v_e_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v_a_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_,
    );
    lean_dec(v_a_619_);
    lean_dec_ref(v_a_618_);
    lean_dec(v_a_617_);
    lean_dec_ref(v_a_616_);
    lean_dec_ref(v_a_615_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
    mut v_e_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
    mut v_a_624_: *mut LeanObject,
    mut v_a_625_: *mut LeanObject,
    mut v_a_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_,
    );
    return v___x_631_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(
    mut v_e_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
    mut v_a_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
    mut v_a_637_: *mut LeanObject,
    mut v_a_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_641_: *mut LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
        v_e_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
    );
    lean_dec(v_a_639_);
    lean_dec_ref(v_a_638_);
    lean_dec(v_a_637_);
    lean_dec_ref(v_a_636_);
    lean_dec_ref(v_a_635_);
    lean_dec(v_a_634_);
    lean_dec_ref(v_a_633_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
    mut v_e_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_implementedBy_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_646_ = lean_ctor_get(v_a_643_, 1);
                v_implementedBy_647_ = lean_ctor_get_uint8(v_config_646_, 2 as u32);
                if v_implementedBy_647_ == 0 {
                    lean_dec(v_e_642_);
                    v___x_648_ = lean_box(0);
                    v___x_649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_649_, 0, v___x_648_);
                    return v___x_649_;
                } else {
                    if lean_obj_tag(v_e_642_) == 3 {
                        v_declName_650_ = lean_ctor_get(v_e_642_, 0);
                        v_us_651_ = lean_ctor_get(v_e_642_, 1);
                        v_args_652_ = lean_ctor_get(v_e_642_, 2);
                        v_isSharedCheck_673_ = (!lean_is_exclusive(v_e_642_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_654_ = v_e_642_;
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_args_652_);
                            lean_inc(v_us_651_);
                            lean_inc(v_declName_650_);
                            lean_dec(v_e_642_);
                            v___x_654_ = lean_box(0);
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_e_642_);
                        v___x_674_ = lean_box(0);
                        v___x_675_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_675_, 0, v___x_674_);
                        return v___x_675_;
                    }
                }
            }
            1 => {
                v___x_656_ = lean_st_ref_get(v_a_644_);
                v_env_657_ = lean_ctor_get(v___x_656_, 0);
                lean_inc_ref(v_env_657_);
                lean_dec(v___x_656_);
                v___x_658_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_657_, v_declName_650_);
                if lean_obj_tag(v___x_658_) == 1 {
                    v_val_659_ = lean_ctor_get(v___x_658_, 0);
                    v_isSharedCheck_670_ = (!lean_is_exclusive(v___x_658_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_661_ = v___x_658_;
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_659_);
                        lean_dec(v___x_658_);
                        v___x_661_ = lean_box(0);
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_658_);
                    lean_del_object(v___x_654_);
                    lean_dec_ref(v_args_652_);
                    lean_dec(v_us_651_);
                    v___x_671_ = lean_box(0);
                    v___x_672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_672_, 0, v___x_671_);
                    return v___x_672_;
                }
            }
            2 => {
                if v_isShared_655_ == 0 {
                    lean_ctor_set(v___x_654_, 0, v_val_659_);
                    v___x_664_ = v___x_654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_659_);
                    lean_ctor_set(v_reuseFailAlloc_669_, 1, v_us_651_);
                    lean_ctor_set(v_reuseFailAlloc_669_, 2, v_args_652_);
                    v___x_664_ = v_reuseFailAlloc_669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_662_ == 0 {
                    lean_ctor_set(v___x_661_, 0, v___x_664_);
                    v___x_666_ = v___x_661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_667_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_667_, 0, v___x_666_);
                return v___x_667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(
    mut v_e_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_676_, v_a_677_, v_a_678_);
    lean_dec(v_a_678_);
    lean_dec_ref(v_a_677_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
    mut v_e_681_: *mut LeanObject,
    mut v_a_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_681_, v_a_682_, v_a_688_);
    return v___x_690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(
    mut v_e_691_: *mut LeanObject,
    mut v_a_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
    mut v_a_694_: *mut LeanObject,
    mut v_a_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
        v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_,
    );
    lean_dec(v_a_698_);
    lean_dec_ref(v_a_697_);
    lean_dec(v_a_696_);
    lean_dec_ref(v_a_695_);
    lean_dec_ref(v_a_694_);
    lean_dec(v_a_693_);
    lean_dec_ref(v_a_692_);
    return v_res_700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
    mut v_e_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
    mut v_a_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_701_, v_a_703_, v_a_705_, v_a_707_);
    if lean_obj_tag(v___x_709_) == 0 {
        let mut v_a_710_: *mut LeanObject = core::ptr::null_mut();
        v_a_710_ = lean_ctor_get(v___x_709_, 0);
        lean_inc(v_a_710_);
        if lean_obj_tag(v_a_710_) == 0 {
            let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_709_, 1);
            v___x_711_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_701_, v_a_705_);
            if lean_obj_tag(v___x_711_) == 0 {
                let mut v_a_712_: *mut LeanObject = core::ptr::null_mut();
                v_a_712_ = lean_ctor_get(v___x_711_, 0);
                lean_inc(v_a_712_);
                if lean_obj_tag(v_a_712_) == 0 {
                    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_711_, 1);
                    lean_inc(v_e_701_);
                    v___x_713_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
                        v_e_701_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_,
                    );
                    if lean_obj_tag(v___x_713_) == 0 {
                        let mut v_a_714_: *mut LeanObject = core::ptr::null_mut();
                        v_a_714_ = lean_ctor_get(v___x_713_, 0);
                        lean_inc(v_a_714_);
                        if lean_obj_tag(v_a_714_) == 0 {
                            let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_713_, 1);
                            v___x_715_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
                                v_e_701_, v_a_702_, v_a_707_,
                            );
                            return v___x_715_;
                        } else {
                            lean_dec_ref_known(v_a_714_, 1);
                            lean_dec(v_e_701_);
                            return v___x_713_;
                        }
                    } else {
                        lean_dec(v_e_701_);
                        return v___x_713_;
                    }
                } else {
                    lean_dec_ref_known(v_a_712_, 1);
                    lean_dec(v_e_701_);
                    return v___x_711_;
                }
            } else {
                lean_dec(v_e_701_);
                return v___x_711_;
            }
        } else {
            lean_dec_ref_known(v_a_710_, 1);
            lean_dec(v_e_701_);
            return v___x_709_;
        }
    } else {
        lean_dec(v_e_701_);
        return v___x_709_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(
    mut v_e_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
    mut v_a_720_: *mut LeanObject,
    mut v_a_721_: *mut LeanObject,
    mut v_a_722_: *mut LeanObject,
    mut v_a_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_,
    );
    lean_dec(v_a_722_);
    lean_dec_ref(v_a_721_);
    lean_dec(v_a_720_);
    lean_dec_ref(v_a_719_);
    lean_dec_ref(v_a_718_);
    lean_dec_ref(v_a_717_);
    return v_res_724_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
    mut v_e_725_: *mut LeanObject,
    mut v_a_726_: *mut LeanObject,
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    v___x_734_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_725_, v_a_726_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
    );
    return v___x_734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(
    mut v_e_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
        v_e_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_,
    );
    lean_dec(v_a_742_);
    lean_dec_ref(v_a_741_);
    lean_dec(v_a_740_);
    lean_dec_ref(v_a_739_);
    lean_dec_ref(v_a_738_);
    lean_dec(v_a_737_);
    lean_dec_ref(v_a_736_);
    return v_res_744_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
}
