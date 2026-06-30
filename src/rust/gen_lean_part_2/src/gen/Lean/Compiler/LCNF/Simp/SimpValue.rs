// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpValue
// Imports: Lean.Compiler.LCNF.Simp.SimpM
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_st_ref_get,
};
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
pub static l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(
    mut v_e_373_: *mut leanh::LeanObject,
    mut v_a_374_: *mut leanh::LeanObject,
    mut v_a_375_: *mut leanh::LeanObject,
    mut v_a_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_idx_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_384_: u8 = 0;
    let mut v_val_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v_val_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_411_: u8 = 0;
    let mut v_a_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_373_) == 2 {
                    v_idx_378_ = leanh::lean_ctor_get(v_e_373_, 1);
                    v_struct_379_ = leanh::lean_ctor_get(v_e_373_, 2);
                    v___x_380_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                        v_struct_379_,
                        v_a_374_,
                        v_a_375_,
                        v_a_376_,
                    );
                    if leanh::lean_obj_tag(v___x_380_) == 0 {
                        v_a_381_ = leanh::lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_411_ = (!leanh::lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_411_ == 0 {
                            v___x_383_ = v___x_380_;
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_381_);
                            leanh::lean_dec(v___x_380_);
                            v___x_383_ = leanh::lean_box(0);
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_412_ = leanh::lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_419_ = (!leanh::lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_419_ == 0 {
                            v___x_414_ = v___x_380_;
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_412_);
                            leanh::lean_dec(v___x_380_);
                            v___x_414_ = leanh::lean_box(0);
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_420_ = leanh::lean_box(0);
                    v___x_421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
                    return v___x_421_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_381_) == 1 {
                    v_val_385_ = leanh::lean_ctor_get(v_a_381_, 0);
                    v_isSharedCheck_406_ = (!leanh::lean_is_exclusive(v_a_381_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v___x_387_ = v_a_381_;
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_385_);
                        leanh::lean_dec(v_a_381_);
                        v___x_387_ = leanh::lean_box(0);
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_381_);
                    v___x_407_ = leanh::lean_box(0);
                    if v_isShared_384_ == 0 {
                        leanh::lean_ctor_set(v___x_383_, 0, v___x_407_);
                        v___x_409_ = v___x_383_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
                        v___x_409_ = v_reuseFailAlloc_410_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_val_385_) == 0 {
                    v_val_389_ = leanh::lean_ctor_get(v_val_385_, 0);
                    leanh::lean_inc_ref(v_val_389_);
                    v_args_390_ = leanh::lean_ctor_get(v_val_385_, 1);
                    leanh::lean_inc_ref(v_args_390_);
                    leanh::lean_dec_ref_known(v_val_385_, 2);
                    v_numParams_391_ = leanh::lean_ctor_get(v_val_389_, 3);
                    leanh::lean_inc(v_numParams_391_);
                    leanh::lean_dec_ref(v_val_389_);
                    v___x_392_ = leanh::lean_box(0);
                    v___x_393_ = lean_nat_add(v_numParams_391_, v_idx_378_);
                    leanh::lean_dec(v_numParams_391_);
                    v___x_394_ = lean_array_get(v___x_392_, v_args_390_, v___x_393_);
                    leanh::lean_dec(v___x_393_);
                    leanh::lean_dec_ref(v_args_390_);
                    v___x_395_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_394_);
                    leanh::lean_dec(v___x_394_);
                    if v_isShared_388_ == 0 {
                        leanh::lean_ctor_set(v___x_387_, 0, v___x_395_);
                        v___x_397_ = v___x_387_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_401_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_395_);
                        v___x_397_ = v_reuseFailAlloc_401_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_val_385_, 1);
                    leanh::lean_del_object(v___x_387_);
                    v___x_402_ = leanh::lean_box(0);
                    if v_isShared_384_ == 0 {
                        leanh::lean_ctor_set(v___x_383_, 0, v___x_402_);
                        v___x_404_ = v___x_383_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
                        v___x_404_ = v_reuseFailAlloc_405_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_384_ == 0 {
                    leanh::lean_ctor_set(v___x_383_, 0, v___x_397_);
                    v___x_399_ = v___x_383_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_400_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
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
                    v_reuseFailAlloc_418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
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
    mut v_e_422_: *mut leanh::LeanObject,
    mut v_a_423_: *mut leanh::LeanObject,
    mut v_a_424_: *mut leanh::LeanObject,
    mut v_a_425_: *mut leanh::LeanObject,
    mut v_a_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_427_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_422_, v_a_423_, v_a_424_, v_a_425_);
    leanh::lean_dec(v_a_425_);
    leanh::lean_dec(v_a_424_);
    leanh::lean_dec_ref(v_a_423_);
    leanh::lean_dec(v_e_422_);
    return v_res_427_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
    mut v_e_428_: *mut leanh::LeanObject,
    mut v_a_429_: *mut leanh::LeanObject,
    mut v_a_430_: *mut leanh::LeanObject,
    mut v_a_431_: *mut leanh::LeanObject,
    mut v_a_432_: *mut leanh::LeanObject,
    mut v_a_433_: *mut leanh::LeanObject,
    mut v_a_434_: *mut leanh::LeanObject,
    mut v_a_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_428_, v_a_431_, v_a_433_, v_a_435_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(
    mut v_e_438_: *mut leanh::LeanObject,
    mut v_a_439_: *mut leanh::LeanObject,
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_a_441_: *mut leanh::LeanObject,
    mut v_a_442_: *mut leanh::LeanObject,
    mut v_a_443_: *mut leanh::LeanObject,
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_a_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
        v_e_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
    );
    leanh::lean_dec(v_a_445_);
    leanh::lean_dec_ref(v_a_444_);
    leanh::lean_dec(v_a_443_);
    leanh::lean_dec_ref(v_a_442_);
    leanh::lean_dec_ref(v_a_441_);
    leanh::lean_dec(v_a_440_);
    leanh::lean_dec_ref(v_a_439_);
    leanh::lean_dec(v_e_438_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(
    mut v_e_450_: *mut leanh::LeanObject,
    mut v_a_451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v_val_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v_value_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_475_: u8 = 0;
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_493_: u8 = 0;
    let mut v_fvarId_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v_a_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_450_) == 4 {
                    v_fvarId_453_ = leanh::lean_ctor_get(v_e_450_, 0);
                    v_args_454_ = leanh::lean_ctor_get(v_e_450_, 1);
                    v___x_455_ = 0;
                    v___x_456_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                        v___x_455_,
                        v_fvarId_453_,
                        v_a_451_,
                    );
                    if leanh::lean_obj_tag(v___x_456_) == 0 {
                        v_a_457_ = leanh::lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_526_ = (!leanh::lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_526_ == 0 {
                            v___x_459_ = v___x_456_;
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_457_);
                            leanh::lean_dec(v___x_456_);
                            v___x_459_ = leanh::lean_box(0);
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_527_ = leanh::lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_534_ = (!leanh::lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_534_ == 0 {
                            v___x_529_ = v___x_456_;
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_527_);
                            leanh::lean_dec(v___x_456_);
                            v___x_529_ = leanh::lean_box(0);
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    v___x_535_ = leanh::lean_box(0);
                    v___x_536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_457_) == 1 {
                    v_val_461_ = leanh::lean_ctor_get(v_a_457_, 0);
                    v_isSharedCheck_521_ = (!leanh::lean_is_exclusive(v_a_457_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_463_ = v_a_457_;
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_461_);
                        leanh::lean_dec(v_a_457_);
                        v___x_463_ = leanh::lean_box(0);
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_457_);
                    v___x_522_ = leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        leanh::lean_ctor_set(v___x_459_, 0, v___x_522_);
                        v___x_524_ = v___x_459_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
                        v___x_524_ = v_reuseFailAlloc_525_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_value_465_ = leanh::lean_ctor_get(v_val_461_, 3);
                leanh::lean_inc(v_value_465_);
                leanh::lean_dec(v_val_461_);
                match leanh::lean_obj_tag(v_value_465_) {
                    1 => {
                        leanh::lean_del_object(v___x_463_);
                        v___x_466_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0;
                        if v_isShared_460_ == 0 {
                            leanh::lean_ctor_set(v___x_459_, 0, v___x_466_);
                            v___x_468_ = v___x_459_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
                            v___x_468_ = v_reuseFailAlloc_469_;
                            state = 3;
                            continue;
                        }
                    }
                    3 => {
                        v_declName_470_ = leanh::lean_ctor_get(v_value_465_, 0);
                        v_us_471_ = leanh::lean_ctor_get(v_value_465_, 1);
                        v_args_472_ = leanh::lean_ctor_get(v_value_465_, 2);
                        v_isSharedCheck_493_ =
                            (!leanh::lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_493_ == 0 {
                            v___x_474_ = v_value_465_;
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_472_);
                            leanh::lean_inc(v_us_471_);
                            leanh::lean_inc(v_declName_470_);
                            leanh::lean_dec(v_value_465_);
                            v___x_474_ = leanh::lean_box(0);
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        }
                    }
                    4 => {
                        v_fvarId_494_ = leanh::lean_ctor_get(v_value_465_, 0);
                        v_args_495_ = leanh::lean_ctor_get(v_value_465_, 1);
                        v_isSharedCheck_516_ =
                            (!leanh::lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_516_ == 0 {
                            v___x_497_ = v_value_465_;
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_495_);
                            leanh::lean_inc(v_fvarId_494_);
                            leanh::lean_dec(v_value_465_);
                            v___x_497_ = leanh::lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_value_465_);
                        leanh::lean_del_object(v___x_463_);
                        v___x_517_ = leanh::lean_box(0);
                        if v_isShared_460_ == 0 {
                            leanh::lean_ctor_set(v___x_459_, 0, v___x_517_);
                            v___x_519_ = v___x_459_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
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
                v___x_477_ = leanh::lean_unsigned_to_nat(0);
                v___x_478_ = lean_nat_dec_eq(v___x_476_, v___x_477_);
                if v___x_478_ == 0 {
                    v___x_479_ = l_Array_append___redArg(v_args_472_, v_args_454_);
                    if v_isShared_475_ == 0 {
                        leanh::lean_ctor_set(v___x_474_, 2, v___x_479_);
                        v___x_481_ = v___x_474_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_488_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v_declName_470_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_488_, 1, v_us_471_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_479_);
                        v___x_481_ = v_reuseFailAlloc_488_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_474_);
                    leanh::lean_dec_ref(v_args_472_);
                    leanh::lean_dec(v_us_471_);
                    leanh::lean_dec(v_declName_470_);
                    leanh::lean_del_object(v___x_463_);
                    v___x_489_ = leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        leanh::lean_ctor_set(v___x_459_, 0, v___x_489_);
                        v___x_491_ = v___x_459_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
                        v___x_491_ = v_reuseFailAlloc_492_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_464_ == 0 {
                    leanh::lean_ctor_set(v___x_463_, 0, v___x_481_);
                    v___x_483_ = v___x_463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
                    v___x_483_ = v_reuseFailAlloc_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_460_ == 0 {
                    leanh::lean_ctor_set(v___x_459_, 0, v___x_483_);
                    v___x_485_ = v___x_459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
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
                v___x_500_ = leanh::lean_unsigned_to_nat(0);
                v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
                if v___x_501_ == 0 {
                    v___x_502_ = l_Array_append___redArg(v_args_495_, v_args_454_);
                    if v_isShared_498_ == 0 {
                        leanh::lean_ctor_set(v___x_497_, 1, v___x_502_);
                        v___x_504_ = v___x_497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_511_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fvarId_494_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_502_);
                        v___x_504_ = v_reuseFailAlloc_511_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_497_);
                    leanh::lean_dec_ref(v_args_495_);
                    leanh::lean_dec(v_fvarId_494_);
                    leanh::lean_del_object(v___x_463_);
                    v___x_512_ = leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        leanh::lean_ctor_set(v___x_459_, 0, v___x_512_);
                        v___x_514_ = v___x_459_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                        v___x_514_ = v_reuseFailAlloc_515_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_464_ == 0 {
                    leanh::lean_ctor_set(v___x_463_, 0, v___x_504_);
                    v___x_506_ = v___x_463_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
                    v___x_506_ = v_reuseFailAlloc_510_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_460_ == 0 {
                    leanh::lean_ctor_set(v___x_459_, 0, v___x_506_);
                    v___x_508_ = v___x_459_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
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
                    v_reuseFailAlloc_533_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
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
    mut v_e_537_: *mut leanh::LeanObject,
    mut v_a_538_: *mut leanh::LeanObject,
    mut v_a_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_537_, v_a_538_);
    leanh::lean_dec(v_a_538_);
    leanh::lean_dec(v_e_537_);
    return v_res_540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
    mut v_e_541_: *mut leanh::LeanObject,
    mut v_a_542_: *mut leanh::LeanObject,
    mut v_a_543_: *mut leanh::LeanObject,
    mut v_a_544_: *mut leanh::LeanObject,
    mut v_a_545_: *mut leanh::LeanObject,
    mut v_a_546_: *mut leanh::LeanObject,
    mut v_a_547_: *mut leanh::LeanObject,
    mut v_a_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_541_, v_a_546_);
    return v___x_550_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(
    mut v_e_551_: *mut leanh::LeanObject,
    mut v_a_552_: *mut leanh::LeanObject,
    mut v_a_553_: *mut leanh::LeanObject,
    mut v_a_554_: *mut leanh::LeanObject,
    mut v_a_555_: *mut leanh::LeanObject,
    mut v_a_556_: *mut leanh::LeanObject,
    mut v_a_557_: *mut leanh::LeanObject,
    mut v_a_558_: *mut leanh::LeanObject,
    mut v_a_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
        v_e_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_,
    );
    leanh::lean_dec(v_a_558_);
    leanh::lean_dec_ref(v_a_557_);
    leanh::lean_dec(v_a_556_);
    leanh::lean_dec_ref(v_a_555_);
    leanh::lean_dec_ref(v_a_554_);
    leanh::lean_dec(v_a_553_);
    leanh::lean_dec_ref(v_a_552_);
    leanh::lean_dec(v_e_551_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
    mut v_e_563_: *mut leanh::LeanObject,
    mut v_a_564_: *mut leanh::LeanObject,
    mut v_a_565_: *mut leanh::LeanObject,
    mut v_a_566_: *mut leanh::LeanObject,
    mut v_a_567_: *mut leanh::LeanObject,
    mut v_a_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v_val_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v_a_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_563_) == 3 {
                    v_declName_573_ = leanh::lean_ctor_get(v_e_563_, 0);
                    v___x_574_ = lean_st_ref_get(v_a_568_);
                    v_env_575_ = leanh::lean_ctor_get(v___x_574_, 0);
                    leanh::lean_inc_ref(v_env_575_);
                    leanh::lean_dec(v___x_574_);
                    v___x_576_ = 0;
                    leanh::lean_inc(v_declName_573_);
                    v___x_577_ =
                        l_Lean_Environment_find_x3f(v_env_575_, v_declName_573_, v___x_576_);
                    if leanh::lean_obj_tag(v___x_577_) == 1 {
                        v_val_578_ = leanh::lean_ctor_get(v___x_577_, 0);
                        leanh::lean_inc(v_val_578_);
                        leanh::lean_dec_ref_known(v___x_577_, 1);
                        if leanh::lean_obj_tag(v_val_578_) == 6 {
                            leanh::lean_dec_ref_known(v_val_578_, 1);
                            v___x_579_ = 0;
                            v___x_580_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_579_, v_e_563_);
                            v___x_581_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
                                v___x_580_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_,
                            );
                            if leanh::lean_obj_tag(v___x_581_) == 0 {
                                v_a_582_ = leanh::lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_603_ =
                                    (!leanh::lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_603_ == 0 {
                                    v___x_584_ = v___x_581_;
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_582_);
                                    leanh::lean_dec(v___x_581_);
                                    v___x_584_ = leanh::lean_box(0);
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_604_ = leanh::lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_611_ =
                                    (!leanh::lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_611_ == 0 {
                                    v___x_606_ = v___x_581_;
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_604_);
                                    leanh::lean_dec(v___x_581_);
                                    v___x_606_ = leanh::lean_box(0);
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_578_);
                            leanh::lean_dec_ref_known(v_e_563_, 3);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_577_);
                        leanh::lean_dec_ref_known(v_e_563_, 3);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_e_563_);
                    v___x_612_ = leanh::lean_box(0);
                    v___x_613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_613_, 0, v___x_612_);
                    return v___x_613_;
                }
            }
            1 => {
                v___x_571_ = leanh::lean_box(0);
                v___x_572_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_572_, 0, v___x_571_);
                return v___x_572_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_582_) == 1 {
                    v_val_586_ = leanh::lean_ctor_get(v_a_582_, 0);
                    v_isSharedCheck_598_ = (!leanh::lean_is_exclusive(v_a_582_)) as u8;
                    if v_isSharedCheck_598_ == 0 {
                        v___x_588_ = v_a_582_;
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_586_);
                        leanh::lean_dec(v_a_582_);
                        v___x_588_ = leanh::lean_box(0);
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_582_);
                    v___x_599_ = leanh::lean_box(0);
                    if v_isShared_585_ == 0 {
                        leanh::lean_ctor_set(v___x_584_, 0, v___x_599_);
                        v___x_601_ = v___x_584_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
                        v___x_601_ = v_reuseFailAlloc_602_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_590_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0;
                v___x_591_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_591_, 0, v_val_586_);
                leanh::lean_ctor_set(v___x_591_, 1, v___x_590_);
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 0, v___x_591_);
                    v___x_593_ = v___x_588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
                    v___x_593_ = v_reuseFailAlloc_597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_585_ == 0 {
                    leanh::lean_ctor_set(v___x_584_, 0, v___x_593_);
                    v___x_595_ = v___x_584_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
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
                    v_reuseFailAlloc_610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
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
    mut v_e_614_: *mut leanh::LeanObject,
    mut v_a_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
    mut v_a_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_,
    );
    leanh::lean_dec(v_a_619_);
    leanh::lean_dec_ref(v_a_618_);
    leanh::lean_dec(v_a_617_);
    leanh::lean_dec_ref(v_a_616_);
    leanh::lean_dec_ref(v_a_615_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
    mut v_e_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_a_624_: *mut leanh::LeanObject,
    mut v_a_625_: *mut leanh::LeanObject,
    mut v_a_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_,
    );
    return v___x_631_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(
    mut v_e_632_: *mut leanh::LeanObject,
    mut v_a_633_: *mut leanh::LeanObject,
    mut v_a_634_: *mut leanh::LeanObject,
    mut v_a_635_: *mut leanh::LeanObject,
    mut v_a_636_: *mut leanh::LeanObject,
    mut v_a_637_: *mut leanh::LeanObject,
    mut v_a_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
        v_e_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
    );
    leanh::lean_dec(v_a_639_);
    leanh::lean_dec_ref(v_a_638_);
    leanh::lean_dec(v_a_637_);
    leanh::lean_dec_ref(v_a_636_);
    leanh::lean_dec_ref(v_a_635_);
    leanh::lean_dec(v_a_634_);
    leanh::lean_dec_ref(v_a_633_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
    mut v_e_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
    mut v_a_644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_config_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implementedBy_647_: u8 = 0;
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_646_ = leanh::lean_ctor_get(v_a_643_, 1);
                v_implementedBy_647_ = leanh::lean_ctor_get_uint8(v_config_646_, 2 as u32);
                if v_implementedBy_647_ == 0 {
                    leanh::lean_dec(v_e_642_);
                    v___x_648_ = leanh::lean_box(0);
                    v___x_649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_649_, 0, v___x_648_);
                    return v___x_649_;
                } else {
                    if leanh::lean_obj_tag(v_e_642_) == 3 {
                        v_declName_650_ = leanh::lean_ctor_get(v_e_642_, 0);
                        v_us_651_ = leanh::lean_ctor_get(v_e_642_, 1);
                        v_args_652_ = leanh::lean_ctor_get(v_e_642_, 2);
                        v_isSharedCheck_673_ = (!leanh::lean_is_exclusive(v_e_642_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_654_ = v_e_642_;
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_652_);
                            leanh::lean_inc(v_us_651_);
                            leanh::lean_inc(v_declName_650_);
                            leanh::lean_dec(v_e_642_);
                            v___x_654_ = leanh::lean_box(0);
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_e_642_);
                        v___x_674_ = leanh::lean_box(0);
                        v___x_675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_675_, 0, v___x_674_);
                        return v___x_675_;
                    }
                }
            }
            1 => {
                v___x_656_ = lean_st_ref_get(v_a_644_);
                v_env_657_ = leanh::lean_ctor_get(v___x_656_, 0);
                leanh::lean_inc_ref(v_env_657_);
                leanh::lean_dec(v___x_656_);
                v___x_658_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_657_, v_declName_650_);
                if leanh::lean_obj_tag(v___x_658_) == 1 {
                    v_val_659_ = leanh::lean_ctor_get(v___x_658_, 0);
                    v_isSharedCheck_670_ = (!leanh::lean_is_exclusive(v___x_658_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_661_ = v___x_658_;
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_659_);
                        leanh::lean_dec(v___x_658_);
                        v___x_661_ = leanh::lean_box(0);
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_658_);
                    leanh::lean_del_object(v___x_654_);
                    leanh::lean_dec_ref(v_args_652_);
                    leanh::lean_dec(v_us_651_);
                    v___x_671_ = leanh::lean_box(0);
                    v___x_672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_672_, 0, v___x_671_);
                    return v___x_672_;
                }
            }
            2 => {
                if v_isShared_655_ == 0 {
                    leanh::lean_ctor_set(v___x_654_, 0, v_val_659_);
                    v___x_664_ = v___x_654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_669_, 1, v_us_651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_669_, 2, v_args_652_);
                    v___x_664_ = v_reuseFailAlloc_669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_662_ == 0 {
                    leanh::lean_ctor_set(v___x_661_, 0, v___x_664_);
                    v___x_666_ = v___x_661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_667_, 0, v___x_666_);
                return v___x_667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(
    mut v_e_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
    mut v_a_678_: *mut leanh::LeanObject,
    mut v_a_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_676_, v_a_677_, v_a_678_);
    leanh::lean_dec(v_a_678_);
    leanh::lean_dec_ref(v_a_677_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
    mut v_e_681_: *mut leanh::LeanObject,
    mut v_a_682_: *mut leanh::LeanObject,
    mut v_a_683_: *mut leanh::LeanObject,
    mut v_a_684_: *mut leanh::LeanObject,
    mut v_a_685_: *mut leanh::LeanObject,
    mut v_a_686_: *mut leanh::LeanObject,
    mut v_a_687_: *mut leanh::LeanObject,
    mut v_a_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_681_, v_a_682_, v_a_688_);
    return v___x_690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(
    mut v_e_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_a_694_: *mut leanh::LeanObject,
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
    mut v_a_698_: *mut leanh::LeanObject,
    mut v_a_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
        v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_,
    );
    leanh::lean_dec(v_a_698_);
    leanh::lean_dec_ref(v_a_697_);
    leanh::lean_dec(v_a_696_);
    leanh::lean_dec_ref(v_a_695_);
    leanh::lean_dec_ref(v_a_694_);
    leanh::lean_dec(v_a_693_);
    leanh::lean_dec_ref(v_a_692_);
    return v_res_700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
    mut v_e_701_: *mut leanh::LeanObject,
    mut v_a_702_: *mut leanh::LeanObject,
    mut v_a_703_: *mut leanh::LeanObject,
    mut v_a_704_: *mut leanh::LeanObject,
    mut v_a_705_: *mut leanh::LeanObject,
    mut v_a_706_: *mut leanh::LeanObject,
    mut v_a_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_701_, v_a_703_, v_a_705_, v_a_707_);
    if leanh::lean_obj_tag(v___x_709_) == 0 {
        let mut v_a_710_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_710_ = leanh::lean_ctor_get(v___x_709_, 0);
        leanh::lean_inc(v_a_710_);
        if leanh::lean_obj_tag(v_a_710_) == 0 {
            let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_709_, 1);
            v___x_711_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_701_, v_a_705_);
            if leanh::lean_obj_tag(v___x_711_) == 0 {
                let mut v_a_712_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_712_ = leanh::lean_ctor_get(v___x_711_, 0);
                leanh::lean_inc(v_a_712_);
                if leanh::lean_obj_tag(v_a_712_) == 0 {
                    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref_known(v___x_711_, 1);
                    leanh::lean_inc(v_e_701_);
                    v___x_713_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
                        v_e_701_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_,
                    );
                    if leanh::lean_obj_tag(v___x_713_) == 0 {
                        let mut v_a_714_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_a_714_ = leanh::lean_ctor_get(v___x_713_, 0);
                        leanh::lean_inc(v_a_714_);
                        if leanh::lean_obj_tag(v_a_714_) == 0 {
                            let mut v___x_715_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec_ref_known(v___x_713_, 1);
                            v___x_715_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
                                v_e_701_, v_a_702_, v_a_707_,
                            );
                            return v___x_715_;
                        } else {
                            leanh::lean_dec_ref_known(v_a_714_, 1);
                            leanh::lean_dec(v_e_701_);
                            return v___x_713_;
                        }
                    } else {
                        leanh::lean_dec(v_e_701_);
                        return v___x_713_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_712_, 1);
                    leanh::lean_dec(v_e_701_);
                    return v___x_711_;
                }
            } else {
                leanh::lean_dec(v_e_701_);
                return v___x_711_;
            }
        } else {
            leanh::lean_dec_ref_known(v_a_710_, 1);
            leanh::lean_dec(v_e_701_);
            return v___x_709_;
        }
    } else {
        leanh::lean_dec(v_e_701_);
        return v___x_709_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(
    mut v_e_716_: *mut leanh::LeanObject,
    mut v_a_717_: *mut leanh::LeanObject,
    mut v_a_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_a_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_,
    );
    leanh::lean_dec(v_a_722_);
    leanh::lean_dec_ref(v_a_721_);
    leanh::lean_dec(v_a_720_);
    leanh::lean_dec_ref(v_a_719_);
    leanh::lean_dec_ref(v_a_718_);
    leanh::lean_dec_ref(v_a_717_);
    return v_res_724_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
    mut v_e_725_: *mut leanh::LeanObject,
    mut v_a_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
    mut v_a_728_: *mut leanh::LeanObject,
    mut v_a_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_725_, v_a_726_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
    );
    return v___x_734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(
    mut v_e_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
    mut v_a_739_: *mut leanh::LeanObject,
    mut v_a_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
        v_e_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_,
    );
    leanh::lean_dec(v_a_742_);
    leanh::lean_dec_ref(v_a_741_);
    leanh::lean_dec(v_a_740_);
    leanh::lean_dec_ref(v_a_739_);
    leanh::lean_dec_ref(v_a_738_);
    leanh::lean_dec(v_a_737_);
    leanh::lean_dec_ref(v_a_736_);
    return v_res_744_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_SimpValue(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
}