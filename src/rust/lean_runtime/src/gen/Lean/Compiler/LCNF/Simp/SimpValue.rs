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
pub static l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(
    mut v_e_373_: *mut crate::leanh::LeanObject,
    mut v_a_374_: *mut crate::leanh::LeanObject,
    mut v_a_375_: *mut crate::leanh::LeanObject,
    mut v_a_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_384_: u8 = 0;
    let mut v_val_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v_val_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_411_: u8 = 0;
    let mut v_a_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_373_) == 2 {
                    v_idx_378_ = crate::leanh::lean_ctor_get(v_e_373_, 1);
                    v_struct_379_ = crate::leanh::lean_ctor_get(v_e_373_, 2);
                    v___x_380_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                        v_struct_379_,
                        v_a_374_,
                        v_a_375_,
                        v_a_376_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_380_) == 0 {
                        v_a_381_ = crate::leanh::lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_411_ = (!crate::leanh::lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_411_ == 0 {
                            v___x_383_ = v___x_380_;
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_381_);
                            crate::leanh::lean_dec(v___x_380_);
                            v___x_383_ = crate::leanh::lean_box(0);
                            v_isShared_384_ = v_isSharedCheck_411_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_412_ = crate::leanh::lean_ctor_get(v___x_380_, 0);
                        v_isSharedCheck_419_ = (!crate::leanh::lean_is_exclusive(v___x_380_)) as u8;
                        if v_isSharedCheck_419_ == 0 {
                            v___x_414_ = v___x_380_;
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_412_);
                            crate::leanh::lean_dec(v___x_380_);
                            v___x_414_ = crate::leanh::lean_box(0);
                            v_isShared_415_ = v_isSharedCheck_419_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_420_ = crate::leanh::lean_box(0);
                    v___x_421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
                    return v___x_421_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_381_) == 1 {
                    v_val_385_ = crate::leanh::lean_ctor_get(v_a_381_, 0);
                    v_isSharedCheck_406_ = (!crate::leanh::lean_is_exclusive(v_a_381_)) as u8;
                    if v_isSharedCheck_406_ == 0 {
                        v___x_387_ = v_a_381_;
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_385_);
                        crate::leanh::lean_dec(v_a_381_);
                        v___x_387_ = crate::leanh::lean_box(0);
                        v_isShared_388_ = v_isSharedCheck_406_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_381_);
                    v___x_407_ = crate::leanh::lean_box(0);
                    if v_isShared_384_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_407_);
                        v___x_409_ = v___x_383_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
                        v___x_409_ = v_reuseFailAlloc_410_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_385_) == 0 {
                    v_val_389_ = crate::leanh::lean_ctor_get(v_val_385_, 0);
                    crate::leanh::lean_inc_ref(v_val_389_);
                    v_args_390_ = crate::leanh::lean_ctor_get(v_val_385_, 1);
                    crate::leanh::lean_inc_ref(v_args_390_);
                    crate::leanh::lean_dec_ref_known(v_val_385_, 2);
                    v_numParams_391_ = crate::leanh::lean_ctor_get(v_val_389_, 3);
                    crate::leanh::lean_inc(v_numParams_391_);
                    crate::leanh::lean_dec_ref(v_val_389_);
                    v___x_392_ = crate::leanh::lean_box(0);
                    v___x_393_ = lean_nat_add(v_numParams_391_, v_idx_378_);
                    crate::leanh::lean_dec(v_numParams_391_);
                    v___x_394_ = lean_array_get(v___x_392_, v_args_390_, v___x_393_);
                    crate::leanh::lean_dec(v___x_393_);
                    crate::leanh::lean_dec_ref(v_args_390_);
                    v___x_395_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_394_);
                    crate::leanh::lean_dec(v___x_394_);
                    if v_isShared_388_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_387_, 0, v___x_395_);
                        v___x_397_ = v___x_387_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_401_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_395_);
                        v___x_397_ = v_reuseFailAlloc_401_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_val_385_, 1);
                    crate::leanh::lean_del_object(v___x_387_);
                    v___x_402_ = crate::leanh::lean_box(0);
                    if v_isShared_384_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_402_);
                        v___x_404_ = v___x_383_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
                        v___x_404_ = v_reuseFailAlloc_405_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_383_, 0, v___x_397_);
                    v___x_399_ = v___x_383_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
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
                    v_reuseFailAlloc_418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
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
    mut v_e_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
    mut v_a_424_: *mut crate::leanh::LeanObject,
    mut v_a_425_: *mut crate::leanh::LeanObject,
    mut v_a_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_427_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_422_, v_a_423_, v_a_424_, v_a_425_);
    crate::leanh::lean_dec(v_a_425_);
    crate::leanh::lean_dec(v_a_424_);
    crate::leanh::lean_dec_ref(v_a_423_);
    crate::leanh::lean_dec(v_e_422_);
    return v_res_427_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
    mut v_e_428_: *mut crate::leanh::LeanObject,
    mut v_a_429_: *mut crate::leanh::LeanObject,
    mut v_a_430_: *mut crate::leanh::LeanObject,
    mut v_a_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
    mut v_a_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_437_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_428_, v_a_431_, v_a_433_, v_a_435_);
    return v___x_437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(
    mut v_e_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
    mut v_a_442_: *mut crate::leanh::LeanObject,
    mut v_a_443_: *mut crate::leanh::LeanObject,
    mut v_a_444_: *mut crate::leanh::LeanObject,
    mut v_a_445_: *mut crate::leanh::LeanObject,
    mut v_a_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(
        v_e_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_,
    );
    crate::leanh::lean_dec(v_a_445_);
    crate::leanh::lean_dec_ref(v_a_444_);
    crate::leanh::lean_dec(v_a_443_);
    crate::leanh::lean_dec_ref(v_a_442_);
    crate::leanh::lean_dec_ref(v_a_441_);
    crate::leanh::lean_dec(v_a_440_);
    crate::leanh::lean_dec_ref(v_a_439_);
    crate::leanh::lean_dec(v_e_438_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(
    mut v_e_450_: *mut crate::leanh::LeanObject,
    mut v_a_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v_val_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v_value_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_475_: u8 = 0;
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_493_: u8 = 0;
    let mut v_fvarId_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_526_: u8 = 0;
    let mut v_a_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_530_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_534_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_450_) == 4 {
                    v_fvarId_453_ = crate::leanh::lean_ctor_get(v_e_450_, 0);
                    v_args_454_ = crate::leanh::lean_ctor_get(v_e_450_, 1);
                    v___x_455_ = 0;
                    v___x_456_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                        v___x_455_,
                        v_fvarId_453_,
                        v_a_451_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_456_) == 0 {
                        v_a_457_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_526_ = (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_526_ == 0 {
                            v___x_459_ = v___x_456_;
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_457_);
                            crate::leanh::lean_dec(v___x_456_);
                            v___x_459_ = crate::leanh::lean_box(0);
                            v_isShared_460_ = v_isSharedCheck_526_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_527_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                        v_isSharedCheck_534_ = (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                        if v_isSharedCheck_534_ == 0 {
                            v___x_529_ = v___x_456_;
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_527_);
                            crate::leanh::lean_dec(v___x_456_);
                            v___x_529_ = crate::leanh::lean_box(0);
                            v_isShared_530_ = v_isSharedCheck_534_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    v___x_535_ = crate::leanh::lean_box(0);
                    v___x_536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
                    return v___x_536_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_457_) == 1 {
                    v_val_461_ = crate::leanh::lean_ctor_get(v_a_457_, 0);
                    v_isSharedCheck_521_ = (!crate::leanh::lean_is_exclusive(v_a_457_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_463_ = v_a_457_;
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_461_);
                        crate::leanh::lean_dec(v_a_457_);
                        v___x_463_ = crate::leanh::lean_box(0);
                        v_isShared_464_ = v_isSharedCheck_521_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_457_);
                    v___x_522_ = crate::leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_522_);
                        v___x_524_ = v___x_459_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
                        v___x_524_ = v_reuseFailAlloc_525_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v_value_465_ = crate::leanh::lean_ctor_get(v_val_461_, 3);
                crate::leanh::lean_inc(v_value_465_);
                crate::leanh::lean_dec(v_val_461_);
                match crate::leanh::lean_obj_tag(v_value_465_) {
                    1 => {
                        crate::leanh::lean_del_object(v___x_463_);
                        v___x_466_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg___closed__0;
                        if v_isShared_460_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_466_);
                            v___x_468_ = v___x_459_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
                            v___x_468_ = v_reuseFailAlloc_469_;
                            state = 3;
                            continue;
                        }
                    }
                    3 => {
                        v_declName_470_ = crate::leanh::lean_ctor_get(v_value_465_, 0);
                        v_us_471_ = crate::leanh::lean_ctor_get(v_value_465_, 1);
                        v_args_472_ = crate::leanh::lean_ctor_get(v_value_465_, 2);
                        v_isSharedCheck_493_ =
                            (!crate::leanh::lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_493_ == 0 {
                            v___x_474_ = v_value_465_;
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_472_);
                            crate::leanh::lean_inc(v_us_471_);
                            crate::leanh::lean_inc(v_declName_470_);
                            crate::leanh::lean_dec(v_value_465_);
                            v___x_474_ = crate::leanh::lean_box(0);
                            v_isShared_475_ = v_isSharedCheck_493_;
                            state = 4;
                            continue;
                        }
                    }
                    4 => {
                        v_fvarId_494_ = crate::leanh::lean_ctor_get(v_value_465_, 0);
                        v_args_495_ = crate::leanh::lean_ctor_get(v_value_465_, 1);
                        v_isSharedCheck_516_ =
                            (!crate::leanh::lean_is_exclusive(v_value_465_)) as u8;
                        if v_isSharedCheck_516_ == 0 {
                            v___x_497_ = v_value_465_;
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_495_);
                            crate::leanh::lean_inc(v_fvarId_494_);
                            crate::leanh::lean_dec(v_value_465_);
                            v___x_497_ = crate::leanh::lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_516_;
                            state = 9;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_value_465_);
                        crate::leanh::lean_del_object(v___x_463_);
                        v___x_517_ = crate::leanh::lean_box(0);
                        if v_isShared_460_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_517_);
                            v___x_519_ = v___x_459_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
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
                v___x_477_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_478_ = lean_nat_dec_eq(v___x_476_, v___x_477_);
                if v___x_478_ == 0 {
                    v___x_479_ = l_Array_append___redArg(v_args_472_, v_args_454_);
                    if v_isShared_475_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_474_, 2, v___x_479_);
                        v___x_481_ = v___x_474_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_488_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 0, v_declName_470_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 1, v_us_471_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_479_);
                        v___x_481_ = v_reuseFailAlloc_488_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_474_);
                    crate::leanh::lean_dec_ref(v_args_472_);
                    crate::leanh::lean_dec(v_us_471_);
                    crate::leanh::lean_dec(v_declName_470_);
                    crate::leanh::lean_del_object(v___x_463_);
                    v___x_489_ = crate::leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_489_);
                        v___x_491_ = v___x_459_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
                        v___x_491_ = v_reuseFailAlloc_492_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_481_);
                    v___x_483_ = v___x_463_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_481_);
                    v___x_483_ = v_reuseFailAlloc_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_483_);
                    v___x_485_ = v___x_459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
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
                v___x_500_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
                if v___x_501_ == 0 {
                    v___x_502_ = l_Array_append___redArg(v_args_495_, v_args_454_);
                    if v_isShared_498_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_497_, 1, v___x_502_);
                        v___x_504_ = v___x_497_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_511_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v_fvarId_494_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_502_);
                        v___x_504_ = v_reuseFailAlloc_511_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_497_);
                    crate::leanh::lean_dec_ref(v_args_495_);
                    crate::leanh::lean_dec(v_fvarId_494_);
                    crate::leanh::lean_del_object(v___x_463_);
                    v___x_512_ = crate::leanh::lean_box(0);
                    if v_isShared_460_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_512_);
                        v___x_514_ = v___x_459_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                        v___x_514_ = v_reuseFailAlloc_515_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_463_, 0, v___x_504_);
                    v___x_506_ = v___x_463_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_504_);
                    v___x_506_ = v_reuseFailAlloc_510_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_506_);
                    v___x_508_ = v___x_459_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
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
                    v_reuseFailAlloc_533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
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
    mut v_e_537_: *mut crate::leanh::LeanObject,
    mut v_a_538_: *mut crate::leanh::LeanObject,
    mut v_a_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_537_, v_a_538_);
    crate::leanh::lean_dec(v_a_538_);
    crate::leanh::lean_dec(v_e_537_);
    return v_res_540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
    mut v_e_541_: *mut crate::leanh::LeanObject,
    mut v_a_542_: *mut crate::leanh::LeanObject,
    mut v_a_543_: *mut crate::leanh::LeanObject,
    mut v_a_544_: *mut crate::leanh::LeanObject,
    mut v_a_545_: *mut crate::leanh::LeanObject,
    mut v_a_546_: *mut crate::leanh::LeanObject,
    mut v_a_547_: *mut crate::leanh::LeanObject,
    mut v_a_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_541_, v_a_546_);
    return v___x_550_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(
    mut v_e_551_: *mut crate::leanh::LeanObject,
    mut v_a_552_: *mut crate::leanh::LeanObject,
    mut v_a_553_: *mut crate::leanh::LeanObject,
    mut v_a_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
    mut v_a_556_: *mut crate::leanh::LeanObject,
    mut v_a_557_: *mut crate::leanh::LeanObject,
    mut v_a_558_: *mut crate::leanh::LeanObject,
    mut v_a_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(
        v_e_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_,
    );
    crate::leanh::lean_dec(v_a_558_);
    crate::leanh::lean_dec_ref(v_a_557_);
    crate::leanh::lean_dec(v_a_556_);
    crate::leanh::lean_dec_ref(v_a_555_);
    crate::leanh::lean_dec_ref(v_a_554_);
    crate::leanh::lean_dec(v_a_553_);
    crate::leanh::lean_dec_ref(v_a_552_);
    crate::leanh::lean_dec(v_e_551_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
    mut v_e_563_: *mut crate::leanh::LeanObject,
    mut v_a_564_: *mut crate::leanh::LeanObject,
    mut v_a_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
    mut v_a_567_: *mut crate::leanh::LeanObject,
    mut v_a_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v_val_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_603_: u8 = 0;
    let mut v_a_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_563_) == 3 {
                    v_declName_573_ = crate::leanh::lean_ctor_get(v_e_563_, 0);
                    v___x_574_ = lean_st_ref_get(v_a_568_);
                    v_env_575_ = crate::leanh::lean_ctor_get(v___x_574_, 0);
                    crate::leanh::lean_inc_ref(v_env_575_);
                    crate::leanh::lean_dec(v___x_574_);
                    v___x_576_ = 0;
                    crate::leanh::lean_inc(v_declName_573_);
                    v___x_577_ =
                        l_Lean_Environment_find_x3f(v_env_575_, v_declName_573_, v___x_576_);
                    if crate::leanh::lean_obj_tag(v___x_577_) == 1 {
                        v_val_578_ = crate::leanh::lean_ctor_get(v___x_577_, 0);
                        crate::leanh::lean_inc(v_val_578_);
                        crate::leanh::lean_dec_ref_known(v___x_577_, 1);
                        if crate::leanh::lean_obj_tag(v_val_578_) == 6 {
                            crate::leanh::lean_dec_ref_known(v_val_578_, 1);
                            v___x_579_ = 0;
                            v___x_580_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_579_, v_e_563_);
                            v___x_581_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(
                                v___x_580_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_581_) == 0 {
                                v_a_582_ = crate::leanh::lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_603_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_603_ == 0 {
                                    v___x_584_ = v___x_581_;
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_582_);
                                    crate::leanh::lean_dec(v___x_581_);
                                    v___x_584_ = crate::leanh::lean_box(0);
                                    v_isShared_585_ = v_isSharedCheck_603_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_604_ = crate::leanh::lean_ctor_get(v___x_581_, 0);
                                v_isSharedCheck_611_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_581_)) as u8;
                                if v_isSharedCheck_611_ == 0 {
                                    v___x_606_ = v___x_581_;
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_604_);
                                    crate::leanh::lean_dec(v___x_581_);
                                    v___x_606_ = crate::leanh::lean_box(0);
                                    v_isShared_607_ = v_isSharedCheck_611_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_578_);
                            crate::leanh::lean_dec_ref_known(v_e_563_, 3);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_577_);
                        crate::leanh::lean_dec_ref_known(v_e_563_, 3);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_e_563_);
                    v___x_612_ = crate::leanh::lean_box(0);
                    v___x_613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_613_, 0, v___x_612_);
                    return v___x_613_;
                }
            }
            1 => {
                v___x_571_ = crate::leanh::lean_box(0);
                v___x_572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_572_, 0, v___x_571_);
                return v___x_572_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_582_) == 1 {
                    v_val_586_ = crate::leanh::lean_ctor_get(v_a_582_, 0);
                    v_isSharedCheck_598_ = (!crate::leanh::lean_is_exclusive(v_a_582_)) as u8;
                    if v_isSharedCheck_598_ == 0 {
                        v___x_588_ = v_a_582_;
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_586_);
                        crate::leanh::lean_dec(v_a_582_);
                        v___x_588_ = crate::leanh::lean_box(0);
                        v_isShared_589_ = v_isSharedCheck_598_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_582_);
                    v___x_599_ = crate::leanh::lean_box(0);
                    if v_isShared_585_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_599_);
                        v___x_601_ = v___x_584_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
                        v___x_601_ = v_reuseFailAlloc_602_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_590_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg___closed__0;
                v___x_591_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_591_, 0, v_val_586_);
                crate::leanh::lean_ctor_set(v___x_591_, 1, v___x_590_);
                if v_isShared_589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_588_, 0, v___x_591_);
                    v___x_593_ = v___x_588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_591_);
                    v___x_593_ = v_reuseFailAlloc_597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_593_);
                    v___x_595_ = v___x_584_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
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
                    v_reuseFailAlloc_610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
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
    mut v_e_614_: *mut crate::leanh::LeanObject,
    mut v_a_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
    mut v_a_617_: *mut crate::leanh::LeanObject,
    mut v_a_618_: *mut crate::leanh::LeanObject,
    mut v_a_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_,
    );
    crate::leanh::lean_dec(v_a_619_);
    crate::leanh::lean_dec_ref(v_a_618_);
    crate::leanh::lean_dec(v_a_617_);
    crate::leanh::lean_dec_ref(v_a_616_);
    crate::leanh::lean_dec_ref(v_a_615_);
    return v_res_621_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
    mut v_e_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v_a_624_: *mut crate::leanh::LeanObject,
    mut v_a_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
        v_e_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_,
    );
    return v___x_631_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(
    mut v_e_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
    mut v_a_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
    mut v_a_640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(
        v_e_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
    );
    crate::leanh::lean_dec(v_a_639_);
    crate::leanh::lean_dec_ref(v_a_638_);
    crate::leanh::lean_dec(v_a_637_);
    crate::leanh::lean_dec_ref(v_a_636_);
    crate::leanh::lean_dec_ref(v_a_635_);
    crate::leanh::lean_dec(v_a_634_);
    crate::leanh::lean_dec_ref(v_a_633_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
    mut v_e_642_: *mut crate::leanh::LeanObject,
    mut v_a_643_: *mut crate::leanh::LeanObject,
    mut v_a_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implementedBy_647_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_646_ = crate::leanh::lean_ctor_get(v_a_643_, 1);
                v_implementedBy_647_ = crate::leanh::lean_ctor_get_uint8(v_config_646_, 2 as u32);
                if v_implementedBy_647_ == 0 {
                    crate::leanh::lean_dec(v_e_642_);
                    v___x_648_ = crate::leanh::lean_box(0);
                    v___x_649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_648_);
                    return v___x_649_;
                } else {
                    if crate::leanh::lean_obj_tag(v_e_642_) == 3 {
                        v_declName_650_ = crate::leanh::lean_ctor_get(v_e_642_, 0);
                        v_us_651_ = crate::leanh::lean_ctor_get(v_e_642_, 1);
                        v_args_652_ = crate::leanh::lean_ctor_get(v_e_642_, 2);
                        v_isSharedCheck_673_ = (!crate::leanh::lean_is_exclusive(v_e_642_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_654_ = v_e_642_;
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_652_);
                            crate::leanh::lean_inc(v_us_651_);
                            crate::leanh::lean_inc(v_declName_650_);
                            crate::leanh::lean_dec(v_e_642_);
                            v___x_654_ = crate::leanh::lean_box(0);
                            v_isShared_655_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_e_642_);
                        v___x_674_ = crate::leanh::lean_box(0);
                        v___x_675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_674_);
                        return v___x_675_;
                    }
                }
            }
            1 => {
                v___x_656_ = lean_st_ref_get(v_a_644_);
                v_env_657_ = crate::leanh::lean_ctor_get(v___x_656_, 0);
                crate::leanh::lean_inc_ref(v_env_657_);
                crate::leanh::lean_dec(v___x_656_);
                v___x_658_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_657_, v_declName_650_);
                if crate::leanh::lean_obj_tag(v___x_658_) == 1 {
                    v_val_659_ = crate::leanh::lean_ctor_get(v___x_658_, 0);
                    v_isSharedCheck_670_ = (!crate::leanh::lean_is_exclusive(v___x_658_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_661_ = v___x_658_;
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_659_);
                        crate::leanh::lean_dec(v___x_658_);
                        v___x_661_ = crate::leanh::lean_box(0);
                        v_isShared_662_ = v_isSharedCheck_670_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_658_);
                    crate::leanh::lean_del_object(v___x_654_);
                    crate::leanh::lean_dec_ref(v_args_652_);
                    crate::leanh::lean_dec(v_us_651_);
                    v___x_671_ = crate::leanh::lean_box(0);
                    v___x_672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_671_);
                    return v___x_672_;
                }
            }
            2 => {
                if v_isShared_655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_654_, 0, v_val_659_);
                    v___x_664_ = v___x_654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_669_, 1, v_us_651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_669_, 2, v_args_652_);
                    v___x_664_ = v_reuseFailAlloc_669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_662_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_661_, 0, v___x_664_);
                    v___x_666_ = v___x_661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_667_, 0, v___x_666_);
                return v___x_667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg___boxed(
    mut v_e_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
    mut v_a_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_676_, v_a_677_, v_a_678_);
    crate::leanh::lean_dec(v_a_678_);
    crate::leanh::lean_dec_ref(v_a_677_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
    mut v_e_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
    mut v_a_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
    mut v_a_687_: *mut crate::leanh::LeanObject,
    mut v_a_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ =
        l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(v_e_681_, v_a_682_, v_a_688_);
    return v___x_690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(
    mut v_e_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
    mut v_a_694_: *mut crate::leanh::LeanObject,
    mut v_a_695_: *mut crate::leanh::LeanObject,
    mut v_a_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
    mut v_a_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(
        v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_,
    );
    crate::leanh::lean_dec(v_a_698_);
    crate::leanh::lean_dec_ref(v_a_697_);
    crate::leanh::lean_dec(v_a_696_);
    crate::leanh::lean_dec_ref(v_a_695_);
    crate::leanh::lean_dec_ref(v_a_694_);
    crate::leanh::lean_dec(v_a_693_);
    crate::leanh::lean_dec_ref(v_a_692_);
    return v_res_700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
    mut v_e_701_: *mut crate::leanh::LeanObject,
    mut v_a_702_: *mut crate::leanh::LeanObject,
    mut v_a_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_a_705_: *mut crate::leanh::LeanObject,
    mut v_a_706_: *mut crate::leanh::LeanObject,
    mut v_a_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ =
        l_Lean_Compiler_LCNF_Simp_simpProj_x3f___redArg(v_e_701_, v_a_703_, v_a_705_, v_a_707_);
    if crate::leanh::lean_obj_tag(v___x_709_) == 0 {
        let mut v_a_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_710_ = crate::leanh::lean_ctor_get(v___x_709_, 0);
        crate::leanh::lean_inc(v_a_710_);
        if crate::leanh::lean_obj_tag(v_a_710_) == 0 {
            let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_709_, 1);
            v___x_711_ = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___redArg(v_e_701_, v_a_705_);
            if crate::leanh::lean_obj_tag(v___x_711_) == 0 {
                let mut v_a_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_712_ = crate::leanh::lean_ctor_get(v___x_711_, 0);
                crate::leanh::lean_inc(v_a_712_);
                if crate::leanh::lean_obj_tag(v_a_712_) == 0 {
                    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_711_, 1);
                    crate::leanh::lean_inc(v_e_701_);
                    v___x_713_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___redArg(
                        v_e_701_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_713_) == 0 {
                        let mut v_a_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_714_ = crate::leanh::lean_ctor_get(v___x_713_, 0);
                        crate::leanh::lean_inc(v_a_714_);
                        if crate::leanh::lean_obj_tag(v_a_714_) == 0 {
                            let mut v___x_715_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_713_, 1);
                            v___x_715_ = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___redArg(
                                v_e_701_, v_a_702_, v_a_707_,
                            );
                            return v___x_715_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_714_, 1);
                            crate::leanh::lean_dec(v_e_701_);
                            return v___x_713_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_e_701_);
                        return v___x_713_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_712_, 1);
                    crate::leanh::lean_dec(v_e_701_);
                    return v___x_711_;
                }
            } else {
                crate::leanh::lean_dec(v_e_701_);
                return v___x_711_;
            }
        } else {
            crate::leanh::lean_dec_ref_known(v_a_710_, 1);
            crate::leanh::lean_dec(v_e_701_);
            return v___x_709_;
        }
    } else {
        crate::leanh::lean_dec(v_e_701_);
        return v___x_709_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg___boxed(
    mut v_e_716_: *mut crate::leanh::LeanObject,
    mut v_a_717_: *mut crate::leanh::LeanObject,
    mut v_a_718_: *mut crate::leanh::LeanObject,
    mut v_a_719_: *mut crate::leanh::LeanObject,
    mut v_a_720_: *mut crate::leanh::LeanObject,
    mut v_a_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_,
    );
    crate::leanh::lean_dec(v_a_722_);
    crate::leanh::lean_dec_ref(v_a_721_);
    crate::leanh::lean_dec(v_a_720_);
    crate::leanh::lean_dec_ref(v_a_719_);
    crate::leanh::lean_dec_ref(v_a_718_);
    crate::leanh::lean_dec_ref(v_a_717_);
    return v_res_724_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
    mut v_e_725_: *mut crate::leanh::LeanObject,
    mut v_a_726_: *mut crate::leanh::LeanObject,
    mut v_a_727_: *mut crate::leanh::LeanObject,
    mut v_a_728_: *mut crate::leanh::LeanObject,
    mut v_a_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
        v_e_725_, v_a_726_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
    );
    return v___x_734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(
    mut v_e_735_: *mut crate::leanh::LeanObject,
    mut v_a_736_: *mut crate::leanh::LeanObject,
    mut v_a_737_: *mut crate::leanh::LeanObject,
    mut v_a_738_: *mut crate::leanh::LeanObject,
    mut v_a_739_: *mut crate::leanh::LeanObject,
    mut v_a_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_a_742_: *mut crate::leanh::LeanObject,
    mut v_a_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(
        v_e_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_,
    );
    crate::leanh::lean_dec(v_a_742_);
    crate::leanh::lean_dec_ref(v_a_741_);
    crate::leanh::lean_dec(v_a_740_);
    crate::leanh::lean_dec_ref(v_a_739_);
    crate::leanh::lean_dec_ref(v_a_738_);
    crate::leanh::lean_dec(v_a_737_);
    crate::leanh::lean_dec_ref(v_a_736_);
    return v_res_744_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_SimpValue(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
}
