// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Simproc
// Imports: Lean.Meta.Sym.Simp.Result
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Meta::Sym::Simp::Result::{
    initialize_Lean_Meta_Sym_Simp_Result, l_Lean_Meta_Sym_Simp_mkEqTrans___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_Result,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::l_Lean_Meta_Sym_Simp_Result_withContextDependent;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_11, lean_apply_12, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instAndThenSimproc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instAndThenSimproc___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Simp_instOrElseSimproc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_instOrElseSimproc___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_andThen(
    mut v_f_339_: *mut LeanObject,
    mut v_g_340_: *mut LeanObject,
    mut v_e_u2081_341_: *mut LeanObject,
    mut v_a_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
    mut v_a_346_: *mut LeanObject,
    mut v_a_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
    mut v_a_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_354_: u8 = 0;
    let mut v_contextDependent_355_: u8 = 0;
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_359_: u8 = 0;
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_362_: u8 = 0;
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut v_unused_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_369_: u8 = 0;
    let mut v_contextDependent_370_: u8 = 0;
    let mut v_done_371_: u8 = 0;
    let mut v_e_x27_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_374_: u8 = 0;
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_377_: u8 = 0;
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_382_: u8 = 0;
    let mut v_done_383_: u8 = 0;
    let mut v_contextDependent_384_: u8 = 0;
    let mut v___y_386_: u8 = 0;
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_395_: u8 = 0;
    let mut v_contextDependent_396_: u8 = 0;
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_399_: u8 = 0;
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_404_: u8 = 0;
    let mut v___y_406_: u8 = 0;
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut v_a_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_417_: u8 = 0;
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_421_: u8 = 0;
    let mut v_isSharedCheck_422_: u8 = 0;
    let mut v_isSharedCheck_423_: u8 = 0;
    let mut v_isSharedCheck_424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_350_);
                lean_inc_ref(v_a_349_);
                lean_inc(v_a_348_);
                lean_inc_ref(v_a_347_);
                lean_inc(v_a_346_);
                lean_inc_ref(v_a_345_);
                lean_inc(v_a_344_);
                lean_inc_ref(v_a_343_);
                lean_inc(v_a_342_);
                lean_inc_ref(v_e_u2081_341_);
                v___x_352_ = lean_apply_11(
                    v_f_339_,
                    v_e_u2081_341_,
                    v_a_342_,
                    v_a_343_,
                    v_a_344_,
                    v_a_345_,
                    v_a_346_,
                    v_a_347_,
                    v_a_348_,
                    v_a_349_,
                    v_a_350_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_352_) == 0 {
                    v_a_353_ = lean_ctor_get(v___x_352_, 0);
                    lean_inc(v_a_353_);
                    if lean_obj_tag(v_a_353_) == 0 {
                        v_done_354_ = lean_ctor_get_uint8(v_a_353_, 0 as u32);
                        if v_done_354_ == 0 {
                            lean_dec_ref_known(v___x_352_, 1);
                            v_contextDependent_355_ = lean_ctor_get_uint8(v_a_353_, 1 as u32);
                            lean_dec_ref_known(v_a_353_, 0);
                            lean_inc(v_a_350_);
                            lean_inc_ref(v_a_349_);
                            lean_inc(v_a_348_);
                            lean_inc_ref(v_a_347_);
                            lean_inc(v_a_346_);
                            lean_inc_ref(v_a_345_);
                            lean_inc(v_a_344_);
                            lean_inc_ref(v_a_343_);
                            lean_inc(v_a_342_);
                            v___x_356_ = lean_apply_11(
                                v_g_340_,
                                v_e_u2081_341_,
                                v_a_342_,
                                v_a_343_,
                                v_a_344_,
                                v_a_345_,
                                v_a_346_,
                                v_a_347_,
                                v_a_348_,
                                v_a_349_,
                                v_a_350_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_356_) == 0 {
                                v_a_357_ = lean_ctor_get(v___x_356_, 0);
                                lean_inc(v_a_357_);
                                if v_contextDependent_355_ == 0 {
                                    lean_dec(v_a_357_);
                                    return v___x_356_;
                                } else {
                                    if lean_obj_tag(v_a_357_) == 0 {
                                        v_contextDependent_369_ =
                                            lean_ctor_get_uint8(v_a_357_, 1 as u32);
                                        v___y_359_ = v_contextDependent_369_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_370_ = lean_ctor_get_uint8(
                                            v_a_357_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_359_ = v_contextDependent_370_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_356_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_353_, 0);
                            lean_dec_ref(v_e_u2081_341_);
                            lean_dec_ref(v_g_340_);
                            return v___x_352_;
                        }
                    } else {
                        v_done_371_ = lean_ctor_get_uint8(
                            v_a_353_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        if v_done_371_ == 0 {
                            lean_dec_ref_known(v___x_352_, 1);
                            v_e_x27_372_ = lean_ctor_get(v_a_353_, 0);
                            v_proof_373_ = lean_ctor_get(v_a_353_, 1);
                            v_contextDependent_374_ = lean_ctor_get_uint8(
                                v_a_353_,
                                (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            );
                            v_isSharedCheck_424_ = (!lean_is_exclusive(v_a_353_)) as u8;
                            if v_isSharedCheck_424_ == 0 {
                                v___x_376_ = v_a_353_;
                                v_isShared_377_ = v_isSharedCheck_424_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_proof_373_);
                                lean_inc(v_e_x27_372_);
                                lean_dec(v_a_353_);
                                v___x_376_ = lean_box(0);
                                v_isShared_377_ = v_isSharedCheck_424_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_a_353_, 2);
                            lean_dec_ref(v_e_u2081_341_);
                            lean_dec_ref(v_g_340_);
                            return v___x_352_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_u2081_341_);
                    lean_dec_ref(v_g_340_);
                    return v___x_352_;
                }
            }
            1 => {
                if v___y_359_ == 0 {
                    v_isSharedCheck_367_ = (!lean_is_exclusive(v___x_356_)) as u8;
                    if v_isSharedCheck_367_ == 0 {
                        v_unused_368_ = lean_ctor_get(v___x_356_, 0);
                        lean_dec(v_unused_368_);
                        v___x_361_ = v___x_356_;
                        v_isShared_362_ = v_isSharedCheck_367_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_356_);
                        v___x_361_ = lean_box(0);
                        v_isShared_362_ = v_isSharedCheck_367_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_357_);
                    return v___x_356_;
                }
            }
            2 => {
                v___x_363_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_357_);
                if v_isShared_362_ == 0 {
                    lean_ctor_set(v___x_361_, 0, v___x_363_);
                    v___x_365_ = v___x_361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
                    v___x_365_ = v_reuseFailAlloc_366_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_365_;
            }
            4 => {
                lean_inc(v_a_350_);
                lean_inc_ref(v_a_349_);
                lean_inc(v_a_348_);
                lean_inc_ref(v_a_347_);
                lean_inc(v_a_346_);
                lean_inc_ref(v_a_345_);
                lean_inc(v_a_344_);
                lean_inc_ref(v_a_343_);
                lean_inc(v_a_342_);
                lean_inc_ref(v_e_x27_372_);
                v___x_378_ = lean_apply_11(
                    v_g_340_,
                    v_e_x27_372_,
                    v_a_342_,
                    v_a_343_,
                    v_a_344_,
                    v_a_345_,
                    v_a_346_,
                    v_a_347_,
                    v_a_348_,
                    v_a_349_,
                    v_a_350_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_378_) == 0 {
                    v_a_379_ = lean_ctor_get(v___x_378_, 0);
                    v_isSharedCheck_423_ = (!lean_is_exclusive(v___x_378_)) as u8;
                    if v_isSharedCheck_423_ == 0 {
                        v___x_381_ = v___x_378_;
                        v_isShared_382_ = v_isSharedCheck_423_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_379_);
                        lean_dec(v___x_378_);
                        v___x_381_ = lean_box(0);
                        v_isShared_382_ = v_isSharedCheck_423_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_376_);
                    lean_dec_ref(v_proof_373_);
                    lean_dec_ref(v_e_x27_372_);
                    lean_dec_ref(v_e_u2081_341_);
                    return v___x_378_;
                }
            }
            5 => {
                if lean_obj_tag(v_a_379_) == 0 {
                    lean_dec_ref(v_e_u2081_341_);
                    v_done_383_ = lean_ctor_get_uint8(v_a_379_, 0 as u32);
                    v_contextDependent_384_ = lean_ctor_get_uint8(v_a_379_, 1 as u32);
                    lean_dec_ref_known(v_a_379_, 0);
                    if v_contextDependent_374_ == 0 {
                        v___y_386_ = v_contextDependent_384_;
                        state = 6;
                        continue;
                    } else {
                        v___y_386_ = v_contextDependent_374_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_381_);
                    lean_del_object(v___x_376_);
                    v_e_x27_393_ = lean_ctor_get(v_a_379_, 0);
                    v_proof_394_ = lean_ctor_get(v_a_379_, 1);
                    v_done_395_ = lean_ctor_get_uint8(
                        v_a_379_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_396_ = lean_ctor_get_uint8(
                        v_a_379_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_422_ = (!lean_is_exclusive(v_a_379_)) as u8;
                    if v_isSharedCheck_422_ == 0 {
                        v___x_398_ = v_a_379_;
                        v_isShared_399_ = v_isSharedCheck_422_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_proof_394_);
                        lean_inc(v_e_x27_393_);
                        lean_dec(v_a_379_);
                        v___x_398_ = lean_box(0);
                        v_isShared_399_ = v_isSharedCheck_422_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_377_ == 0 {
                    v___x_388_ = v___x_376_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_392_, 0, v_e_x27_372_);
                    lean_ctor_set(v_reuseFailAlloc_392_, 1, v_proof_373_);
                    v___x_388_ = v_reuseFailAlloc_392_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_388_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_383_,
                );
                lean_ctor_set_uint8(
                    v___x_388_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_386_,
                );
                if v_isShared_382_ == 0 {
                    lean_ctor_set(v___x_381_, 0, v___x_388_);
                    v___x_390_ = v___x_381_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
                    v___x_390_ = v_reuseFailAlloc_391_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_390_;
            }
            9 => {
                lean_inc_ref(v_e_x27_393_);
                v___x_400_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v_e_u2081_341_,
                    v_e_x27_372_,
                    v_proof_373_,
                    v_e_x27_393_,
                    v_proof_394_,
                    v_a_346_,
                    v_a_347_,
                    v_a_348_,
                    v_a_349_,
                    v_a_350_,
                );
                if lean_obj_tag(v___x_400_) == 0 {
                    v_a_401_ = lean_ctor_get(v___x_400_, 0);
                    v_isSharedCheck_413_ = (!lean_is_exclusive(v___x_400_)) as u8;
                    if v_isSharedCheck_413_ == 0 {
                        v___x_403_ = v___x_400_;
                        v_isShared_404_ = v_isSharedCheck_413_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_401_);
                        lean_dec(v___x_400_);
                        v___x_403_ = lean_box(0);
                        v_isShared_404_ = v_isSharedCheck_413_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_398_);
                    lean_dec_ref(v_e_x27_393_);
                    v_a_414_ = lean_ctor_get(v___x_400_, 0);
                    v_isSharedCheck_421_ = (!lean_is_exclusive(v___x_400_)) as u8;
                    if v_isSharedCheck_421_ == 0 {
                        v___x_416_ = v___x_400_;
                        v_isShared_417_ = v_isSharedCheck_421_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_414_);
                        lean_dec(v___x_400_);
                        v___x_416_ = lean_box(0);
                        v_isShared_417_ = v_isSharedCheck_421_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                if v_contextDependent_374_ == 0 {
                    v___y_406_ = v_contextDependent_396_;
                    state = 11;
                    continue;
                } else {
                    v___y_406_ = v_contextDependent_374_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_399_ == 0 {
                    lean_ctor_set(v___x_398_, 1, v_a_401_);
                    v___x_408_ = v___x_398_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_412_, 0, v_e_x27_393_);
                    lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_401_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_412_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_done_395_,
                    );
                    v___x_408_ = v_reuseFailAlloc_412_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_ctor_set_uint8(
                    v___x_408_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_406_,
                );
                if v_isShared_404_ == 0 {
                    lean_ctor_set(v___x_403_, 0, v___x_408_);
                    v___x_410_ = v___x_403_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
                    v___x_410_ = v_reuseFailAlloc_411_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_410_;
            }
            14 => {
                if v_isShared_417_ == 0 {
                    v___x_419_ = v___x_416_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
                    v___x_419_ = v_reuseFailAlloc_420_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_andThen___boxed(
    mut v_f_425_: *mut LeanObject,
    mut v_g_426_: *mut LeanObject,
    mut v_e_u2081_427_: *mut LeanObject,
    mut v_a_428_: *mut LeanObject,
    mut v_a_429_: *mut LeanObject,
    mut v_a_430_: *mut LeanObject,
    mut v_a_431_: *mut LeanObject,
    mut v_a_432_: *mut LeanObject,
    mut v_a_433_: *mut LeanObject,
    mut v_a_434_: *mut LeanObject,
    mut v_a_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_438_: *mut LeanObject = core::ptr::null_mut();
    v_res_438_ = l_Lean_Meta_Sym_Simp_Simproc_andThen(
        v_f_425_,
        v_g_426_,
        v_e_u2081_427_,
        v_a_428_,
        v_a_429_,
        v_a_430_,
        v_a_431_,
        v_a_432_,
        v_a_433_,
        v_a_434_,
        v_a_435_,
        v_a_436_,
    );
    lean_dec(v_a_436_);
    lean_dec_ref(v_a_435_);
    lean_dec(v_a_434_);
    lean_dec_ref(v_a_433_);
    lean_dec(v_a_432_);
    lean_dec_ref(v_a_431_);
    lean_dec(v_a_430_);
    lean_dec_ref(v_a_429_);
    lean_dec(v_a_428_);
    return v_res_438_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(
    mut v_f_439_: *mut LeanObject,
    mut v_g_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_455_: u8 = 0;
    let mut v_contextDependent_456_: u8 = 0;
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_460_: u8 = 0;
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_463_: u8 = 0;
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut v_unused_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_470_: u8 = 0;
    let mut v_contextDependent_471_: u8 = 0;
    let mut v_done_472_: u8 = 0;
    let mut v_e_x27_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_475_: u8 = 0;
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_483_: u8 = 0;
    let mut v_done_484_: u8 = 0;
    let mut v_contextDependent_485_: u8 = 0;
    let mut v___y_487_: u8 = 0;
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_496_: u8 = 0;
    let mut v_contextDependent_497_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_505_: u8 = 0;
    let mut v___y_507_: u8 = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_514_: u8 = 0;
    let mut v_a_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_522_: u8 = 0;
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut v_isSharedCheck_524_: u8 = 0;
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_450_);
                lean_inc_ref(v___y_449_);
                lean_inc(v___y_448_);
                lean_inc_ref(v___y_447_);
                lean_inc(v___y_446_);
                lean_inc_ref(v___y_445_);
                lean_inc(v___y_444_);
                lean_inc_ref(v___y_443_);
                lean_inc(v___y_442_);
                lean_inc_ref(v___y_441_);
                v___x_452_ = lean_apply_11(
                    v_f_439_,
                    v___y_441_,
                    v___y_442_,
                    v___y_443_,
                    v___y_444_,
                    v___y_445_,
                    v___y_446_,
                    v___y_447_,
                    v___y_448_,
                    v___y_449_,
                    v___y_450_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_452_) == 0 {
                    v_a_453_ = lean_ctor_get(v___x_452_, 0);
                    lean_inc(v_a_453_);
                    v___x_454_ = lean_box(0);
                    if lean_obj_tag(v_a_453_) == 0 {
                        v_done_455_ = lean_ctor_get_uint8(v_a_453_, 0 as u32);
                        if v_done_455_ == 0 {
                            lean_dec_ref_known(v___x_452_, 1);
                            v_contextDependent_456_ = lean_ctor_get_uint8(v_a_453_, 1 as u32);
                            lean_dec_ref_known(v_a_453_, 0);
                            lean_inc(v___y_450_);
                            lean_inc_ref(v___y_449_);
                            lean_inc(v___y_448_);
                            lean_inc_ref(v___y_447_);
                            lean_inc(v___y_446_);
                            lean_inc_ref(v___y_445_);
                            lean_inc(v___y_444_);
                            lean_inc_ref(v___y_443_);
                            lean_inc(v___y_442_);
                            v___x_457_ = lean_apply_12(
                                v_g_440_,
                                v___x_454_,
                                v___y_441_,
                                v___y_442_,
                                v___y_443_,
                                v___y_444_,
                                v___y_445_,
                                v___y_446_,
                                v___y_447_,
                                v___y_448_,
                                v___y_449_,
                                v___y_450_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_457_) == 0 {
                                v_a_458_ = lean_ctor_get(v___x_457_, 0);
                                lean_inc(v_a_458_);
                                if v_contextDependent_456_ == 0 {
                                    lean_dec(v_a_458_);
                                    return v___x_457_;
                                } else {
                                    if lean_obj_tag(v_a_458_) == 0 {
                                        v_contextDependent_470_ =
                                            lean_ctor_get_uint8(v_a_458_, 1 as u32);
                                        v___y_460_ = v_contextDependent_470_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_471_ = lean_ctor_get_uint8(
                                            v_a_458_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_460_ = v_contextDependent_471_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_457_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_453_, 0);
                            lean_dec_ref(v___y_441_);
                            lean_dec_ref(v_g_440_);
                            return v___x_452_;
                        }
                    } else {
                        v_done_472_ = lean_ctor_get_uint8(
                            v_a_453_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        if v_done_472_ == 0 {
                            lean_dec_ref_known(v___x_452_, 1);
                            v_e_x27_473_ = lean_ctor_get(v_a_453_, 0);
                            v_proof_474_ = lean_ctor_get(v_a_453_, 1);
                            v_contextDependent_475_ = lean_ctor_get_uint8(
                                v_a_453_,
                                (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                            );
                            v_isSharedCheck_525_ = (!lean_is_exclusive(v_a_453_)) as u8;
                            if v_isSharedCheck_525_ == 0 {
                                v___x_477_ = v_a_453_;
                                v_isShared_478_ = v_isSharedCheck_525_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_proof_474_);
                                lean_inc(v_e_x27_473_);
                                lean_dec(v_a_453_);
                                v___x_477_ = lean_box(0);
                                v_isShared_478_ = v_isSharedCheck_525_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_a_453_, 2);
                            lean_dec_ref(v___y_441_);
                            lean_dec_ref(v_g_440_);
                            return v___x_452_;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_441_);
                    lean_dec_ref(v_g_440_);
                    return v___x_452_;
                }
            }
            1 => {
                if v___y_460_ == 0 {
                    v_isSharedCheck_468_ = (!lean_is_exclusive(v___x_457_)) as u8;
                    if v_isSharedCheck_468_ == 0 {
                        v_unused_469_ = lean_ctor_get(v___x_457_, 0);
                        lean_dec(v_unused_469_);
                        v___x_462_ = v___x_457_;
                        v_isShared_463_ = v_isSharedCheck_468_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_457_);
                        v___x_462_ = lean_box(0);
                        v_isShared_463_ = v_isSharedCheck_468_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_458_);
                    return v___x_457_;
                }
            }
            2 => {
                v___x_464_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_458_);
                if v_isShared_463_ == 0 {
                    lean_ctor_set(v___x_462_, 0, v___x_464_);
                    v___x_466_ = v___x_462_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
                    v___x_466_ = v_reuseFailAlloc_467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_466_;
            }
            4 => {
                lean_inc(v___y_450_);
                lean_inc_ref(v___y_449_);
                lean_inc(v___y_448_);
                lean_inc_ref(v___y_447_);
                lean_inc(v___y_446_);
                lean_inc_ref(v___y_445_);
                lean_inc(v___y_444_);
                lean_inc_ref(v___y_443_);
                lean_inc(v___y_442_);
                lean_inc_ref(v_e_x27_473_);
                v___x_479_ = lean_apply_12(
                    v_g_440_,
                    v___x_454_,
                    v_e_x27_473_,
                    v___y_442_,
                    v___y_443_,
                    v___y_444_,
                    v___y_445_,
                    v___y_446_,
                    v___y_447_,
                    v___y_448_,
                    v___y_449_,
                    v___y_450_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_479_) == 0 {
                    v_a_480_ = lean_ctor_get(v___x_479_, 0);
                    v_isSharedCheck_524_ = (!lean_is_exclusive(v___x_479_)) as u8;
                    if v_isSharedCheck_524_ == 0 {
                        v___x_482_ = v___x_479_;
                        v_isShared_483_ = v_isSharedCheck_524_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_480_);
                        lean_dec(v___x_479_);
                        v___x_482_ = lean_box(0);
                        v_isShared_483_ = v_isSharedCheck_524_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_477_);
                    lean_dec_ref(v_proof_474_);
                    lean_dec_ref(v_e_x27_473_);
                    lean_dec_ref(v___y_441_);
                    return v___x_479_;
                }
            }
            5 => {
                if lean_obj_tag(v_a_480_) == 0 {
                    lean_dec_ref(v___y_441_);
                    v_done_484_ = lean_ctor_get_uint8(v_a_480_, 0 as u32);
                    v_contextDependent_485_ = lean_ctor_get_uint8(v_a_480_, 1 as u32);
                    lean_dec_ref_known(v_a_480_, 0);
                    if v_contextDependent_475_ == 0 {
                        v___y_487_ = v_contextDependent_485_;
                        state = 6;
                        continue;
                    } else {
                        v___y_487_ = v_contextDependent_475_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_482_);
                    lean_del_object(v___x_477_);
                    v_e_x27_494_ = lean_ctor_get(v_a_480_, 0);
                    v_proof_495_ = lean_ctor_get(v_a_480_, 1);
                    v_done_496_ = lean_ctor_get_uint8(
                        v_a_480_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_contextDependent_497_ = lean_ctor_get_uint8(
                        v_a_480_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_523_ = (!lean_is_exclusive(v_a_480_)) as u8;
                    if v_isSharedCheck_523_ == 0 {
                        v___x_499_ = v_a_480_;
                        v_isShared_500_ = v_isSharedCheck_523_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_proof_495_);
                        lean_inc(v_e_x27_494_);
                        lean_dec(v_a_480_);
                        v___x_499_ = lean_box(0);
                        v_isShared_500_ = v_isSharedCheck_523_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_478_ == 0 {
                    v___x_489_ = v___x_477_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_493_, 0, v_e_x27_473_);
                    lean_ctor_set(v_reuseFailAlloc_493_, 1, v_proof_474_);
                    v___x_489_ = v_reuseFailAlloc_493_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_489_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_done_484_,
                );
                lean_ctor_set_uint8(
                    v___x_489_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_487_,
                );
                if v_isShared_483_ == 0 {
                    lean_ctor_set(v___x_482_, 0, v___x_489_);
                    v___x_491_ = v___x_482_;
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
            8 => {
                return v___x_491_;
            }
            9 => {
                lean_inc_ref(v_e_x27_494_);
                v___x_501_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v___y_441_,
                    v_e_x27_473_,
                    v_proof_474_,
                    v_e_x27_494_,
                    v_proof_495_,
                    v___y_446_,
                    v___y_447_,
                    v___y_448_,
                    v___y_449_,
                    v___y_450_,
                );
                if lean_obj_tag(v___x_501_) == 0 {
                    v_a_502_ = lean_ctor_get(v___x_501_, 0);
                    v_isSharedCheck_514_ = (!lean_is_exclusive(v___x_501_)) as u8;
                    if v_isSharedCheck_514_ == 0 {
                        v___x_504_ = v___x_501_;
                        v_isShared_505_ = v_isSharedCheck_514_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_502_);
                        lean_dec(v___x_501_);
                        v___x_504_ = lean_box(0);
                        v_isShared_505_ = v_isSharedCheck_514_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_499_);
                    lean_dec_ref(v_e_x27_494_);
                    v_a_515_ = lean_ctor_get(v___x_501_, 0);
                    v_isSharedCheck_522_ = (!lean_is_exclusive(v___x_501_)) as u8;
                    if v_isSharedCheck_522_ == 0 {
                        v___x_517_ = v___x_501_;
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_515_);
                        lean_dec(v___x_501_);
                        v___x_517_ = lean_box(0);
                        v_isShared_518_ = v_isSharedCheck_522_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                if v_contextDependent_475_ == 0 {
                    v___y_507_ = v_contextDependent_497_;
                    state = 11;
                    continue;
                } else {
                    v___y_507_ = v_contextDependent_475_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 1, v_a_502_);
                    v___x_509_ = v___x_499_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 2, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_513_, 0, v_e_x27_494_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 1, v_a_502_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_513_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_done_496_,
                    );
                    v___x_509_ = v_reuseFailAlloc_513_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_ctor_set_uint8(
                    v___x_509_,
                    (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
                    v___y_507_,
                );
                if v_isShared_505_ == 0 {
                    lean_ctor_set(v___x_504_, 0, v___x_509_);
                    v___x_511_ = v___x_504_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
                    v___x_511_ = v_reuseFailAlloc_512_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_511_;
            }
            14 => {
                if v_isShared_518_ == 0 {
                    v___x_520_ = v___x_517_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
                    v___x_520_ = v_reuseFailAlloc_521_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0___boxed(
    mut v_f_526_: *mut LeanObject,
    mut v_g_527_: *mut LeanObject,
    mut v___y_528_: *mut LeanObject,
    mut v___y_529_: *mut LeanObject,
    mut v___y_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
    mut v___y_535_: *mut LeanObject,
    mut v___y_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
    mut v___y_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_539_: *mut LeanObject = core::ptr::null_mut();
    v_res_539_ = l_Lean_Meta_Sym_Simp_instAndThenSimproc___lam__0(
        v_f_526_, v_g_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_,
        v___y_534_, v___y_535_, v___y_536_, v___y_537_,
    );
    lean_dec(v___y_537_);
    lean_dec_ref(v___y_536_);
    lean_dec(v___y_535_);
    lean_dec_ref(v___y_534_);
    lean_dec(v___y_533_);
    lean_dec_ref(v___y_532_);
    lean_dec(v___y_531_);
    lean_dec_ref(v___y_530_);
    lean_dec(v___y_529_);
    return v_res_539_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_orElse(
    mut v_f_542_: *mut LeanObject,
    mut v_g_543_: *mut LeanObject,
    mut v_e_u2081_544_: *mut LeanObject,
    mut v_a_545_: *mut LeanObject,
    mut v_a_546_: *mut LeanObject,
    mut v_a_547_: *mut LeanObject,
    mut v_a_548_: *mut LeanObject,
    mut v_a_549_: *mut LeanObject,
    mut v_a_550_: *mut LeanObject,
    mut v_a_551_: *mut LeanObject,
    mut v_a_552_: *mut LeanObject,
    mut v_a_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_557_: u8 = 0;
    let mut v_contextDependent_558_: u8 = 0;
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_562_: u8 = 0;
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_unused_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_572_: u8 = 0;
    let mut v_contextDependent_573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_553_);
                lean_inc_ref(v_a_552_);
                lean_inc(v_a_551_);
                lean_inc_ref(v_a_550_);
                lean_inc(v_a_549_);
                lean_inc_ref(v_a_548_);
                lean_inc(v_a_547_);
                lean_inc_ref(v_a_546_);
                lean_inc(v_a_545_);
                lean_inc_ref(v_e_u2081_544_);
                v___x_555_ = lean_apply_11(
                    v_f_542_,
                    v_e_u2081_544_,
                    v_a_545_,
                    v_a_546_,
                    v_a_547_,
                    v_a_548_,
                    v_a_549_,
                    v_a_550_,
                    v_a_551_,
                    v_a_552_,
                    v_a_553_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_555_) == 0 {
                    v_a_556_ = lean_ctor_get(v___x_555_, 0);
                    lean_inc(v_a_556_);
                    if lean_obj_tag(v_a_556_) == 0 {
                        v_done_557_ = lean_ctor_get_uint8(v_a_556_, 0 as u32);
                        if v_done_557_ == 0 {
                            lean_dec_ref_known(v___x_555_, 1);
                            v_contextDependent_558_ = lean_ctor_get_uint8(v_a_556_, 1 as u32);
                            lean_dec_ref_known(v_a_556_, 0);
                            lean_inc(v_a_553_);
                            lean_inc_ref(v_a_552_);
                            lean_inc(v_a_551_);
                            lean_inc_ref(v_a_550_);
                            lean_inc(v_a_549_);
                            lean_inc_ref(v_a_548_);
                            lean_inc(v_a_547_);
                            lean_inc_ref(v_a_546_);
                            lean_inc(v_a_545_);
                            v___x_559_ = lean_apply_11(
                                v_g_543_,
                                v_e_u2081_544_,
                                v_a_545_,
                                v_a_546_,
                                v_a_547_,
                                v_a_548_,
                                v_a_549_,
                                v_a_550_,
                                v_a_551_,
                                v_a_552_,
                                v_a_553_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_559_) == 0 {
                                v_a_560_ = lean_ctor_get(v___x_559_, 0);
                                lean_inc(v_a_560_);
                                if v_contextDependent_558_ == 0 {
                                    lean_dec(v_a_560_);
                                    return v___x_559_;
                                } else {
                                    if lean_obj_tag(v_a_560_) == 0 {
                                        v_contextDependent_572_ =
                                            lean_ctor_get_uint8(v_a_560_, 1 as u32);
                                        v___y_562_ = v_contextDependent_572_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_573_ = lean_ctor_get_uint8(
                                            v_a_560_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_562_ = v_contextDependent_573_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_559_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_556_, 0);
                            lean_dec_ref(v_e_u2081_544_);
                            lean_dec_ref(v_g_543_);
                            return v___x_555_;
                        }
                    } else {
                        lean_dec_ref_known(v_a_556_, 2);
                        lean_dec_ref(v_e_u2081_544_);
                        lean_dec_ref(v_g_543_);
                        return v___x_555_;
                    }
                } else {
                    lean_dec_ref(v_e_u2081_544_);
                    lean_dec_ref(v_g_543_);
                    return v___x_555_;
                }
            }
            1 => {
                if v___y_562_ == 0 {
                    v_isSharedCheck_570_ = (!lean_is_exclusive(v___x_559_)) as u8;
                    if v_isSharedCheck_570_ == 0 {
                        v_unused_571_ = lean_ctor_get(v___x_559_, 0);
                        lean_dec(v_unused_571_);
                        v___x_564_ = v___x_559_;
                        v_isShared_565_ = v_isSharedCheck_570_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_559_);
                        v___x_564_ = lean_box(0);
                        v_isShared_565_ = v_isSharedCheck_570_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_560_);
                    return v___x_559_;
                }
            }
            2 => {
                v___x_566_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_560_);
                if v_isShared_565_ == 0 {
                    lean_ctor_set(v___x_564_, 0, v___x_566_);
                    v___x_568_ = v___x_564_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
                    v___x_568_ = v_reuseFailAlloc_569_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_orElse___boxed(
    mut v_f_574_: *mut LeanObject,
    mut v_g_575_: *mut LeanObject,
    mut v_e_u2081_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
    mut v_a_579_: *mut LeanObject,
    mut v_a_580_: *mut LeanObject,
    mut v_a_581_: *mut LeanObject,
    mut v_a_582_: *mut LeanObject,
    mut v_a_583_: *mut LeanObject,
    mut v_a_584_: *mut LeanObject,
    mut v_a_585_: *mut LeanObject,
    mut v_a_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_587_: *mut LeanObject = core::ptr::null_mut();
    v_res_587_ = l_Lean_Meta_Sym_Simp_Simproc_orElse(
        v_f_574_,
        v_g_575_,
        v_e_u2081_576_,
        v_a_577_,
        v_a_578_,
        v_a_579_,
        v_a_580_,
        v_a_581_,
        v_a_582_,
        v_a_583_,
        v_a_584_,
        v_a_585_,
    );
    lean_dec(v_a_585_);
    lean_dec_ref(v_a_584_);
    lean_dec(v_a_583_);
    lean_dec_ref(v_a_582_);
    lean_dec(v_a_581_);
    lean_dec_ref(v_a_580_);
    lean_dec(v_a_579_);
    lean_dec_ref(v_a_578_);
    lean_dec(v_a_577_);
    return v_res_587_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(
    mut v_f_588_: *mut LeanObject,
    mut v_g_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
    mut v___y_593_: *mut LeanObject,
    mut v___y_594_: *mut LeanObject,
    mut v___y_595_: *mut LeanObject,
    mut v___y_596_: *mut LeanObject,
    mut v___y_597_: *mut LeanObject,
    mut v___y_598_: *mut LeanObject,
    mut v___y_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_603_: u8 = 0;
    let mut v_contextDependent_604_: u8 = 0;
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_609_: u8 = 0;
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_unused_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_619_: u8 = 0;
    let mut v_contextDependent_620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_599_);
                lean_inc_ref(v___y_598_);
                lean_inc(v___y_597_);
                lean_inc_ref(v___y_596_);
                lean_inc(v___y_595_);
                lean_inc_ref(v___y_594_);
                lean_inc(v___y_593_);
                lean_inc_ref(v___y_592_);
                lean_inc(v___y_591_);
                lean_inc_ref(v___y_590_);
                v___x_601_ = lean_apply_11(
                    v_f_588_,
                    v___y_590_,
                    v___y_591_,
                    v___y_592_,
                    v___y_593_,
                    v___y_594_,
                    v___y_595_,
                    v___y_596_,
                    v___y_597_,
                    v___y_598_,
                    v___y_599_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_601_) == 0 {
                    v_a_602_ = lean_ctor_get(v___x_601_, 0);
                    lean_inc(v_a_602_);
                    if lean_obj_tag(v_a_602_) == 0 {
                        v_done_603_ = lean_ctor_get_uint8(v_a_602_, 0 as u32);
                        if v_done_603_ == 0 {
                            lean_dec_ref_known(v___x_601_, 1);
                            v_contextDependent_604_ = lean_ctor_get_uint8(v_a_602_, 1 as u32);
                            lean_dec_ref_known(v_a_602_, 0);
                            v___x_605_ = lean_box(0);
                            lean_inc(v___y_599_);
                            lean_inc_ref(v___y_598_);
                            lean_inc(v___y_597_);
                            lean_inc_ref(v___y_596_);
                            lean_inc(v___y_595_);
                            lean_inc_ref(v___y_594_);
                            lean_inc(v___y_593_);
                            lean_inc_ref(v___y_592_);
                            lean_inc(v___y_591_);
                            v___x_606_ = lean_apply_12(
                                v_g_589_,
                                v___x_605_,
                                v___y_590_,
                                v___y_591_,
                                v___y_592_,
                                v___y_593_,
                                v___y_594_,
                                v___y_595_,
                                v___y_596_,
                                v___y_597_,
                                v___y_598_,
                                v___y_599_,
                                lean_box(0),
                            );
                            if lean_obj_tag(v___x_606_) == 0 {
                                v_a_607_ = lean_ctor_get(v___x_606_, 0);
                                lean_inc(v_a_607_);
                                if v_contextDependent_604_ == 0 {
                                    lean_dec(v_a_607_);
                                    return v___x_606_;
                                } else {
                                    if lean_obj_tag(v_a_607_) == 0 {
                                        v_contextDependent_619_ =
                                            lean_ctor_get_uint8(v_a_607_, 1 as u32);
                                        v___y_609_ = v_contextDependent_619_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_contextDependent_620_ = lean_ctor_get_uint8(
                                            v_a_607_,
                                            (core::mem::size_of::<*mut LeanObject>() * 2 + 1)
                                                as u32,
                                        );
                                        v___y_609_ = v_contextDependent_620_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                return v___x_606_;
                            }
                        } else {
                            lean_dec_ref_known(v_a_602_, 0);
                            lean_dec_ref(v___y_590_);
                            lean_dec_ref(v_g_589_);
                            return v___x_601_;
                        }
                    } else {
                        lean_dec_ref_known(v_a_602_, 2);
                        lean_dec_ref(v___y_590_);
                        lean_dec_ref(v_g_589_);
                        return v___x_601_;
                    }
                } else {
                    lean_dec_ref(v___y_590_);
                    lean_dec_ref(v_g_589_);
                    return v___x_601_;
                }
            }
            1 => {
                if v___y_609_ == 0 {
                    v_isSharedCheck_617_ = (!lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_617_ == 0 {
                        v_unused_618_ = lean_ctor_get(v___x_606_, 0);
                        lean_dec(v_unused_618_);
                        v___x_611_ = v___x_606_;
                        v_isShared_612_ = v_isSharedCheck_617_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_606_);
                        v___x_611_ = lean_box(0);
                        v_isShared_612_ = v_isSharedCheck_617_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_607_);
                    return v___x_606_;
                }
            }
            2 => {
                v___x_613_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_607_);
                if v_isShared_612_ == 0 {
                    lean_ctor_set(v___x_611_, 0, v___x_613_);
                    v___x_615_ = v___x_611_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
                    v___x_615_ = v_reuseFailAlloc_616_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0___boxed(
    mut v_f_621_: *mut LeanObject,
    mut v_g_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
    mut v___y_629_: *mut LeanObject,
    mut v___y_630_: *mut LeanObject,
    mut v___y_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_634_: *mut LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Lean_Meta_Sym_Simp_instOrElseSimproc___lam__0(
        v_f_621_, v_g_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_,
        v___y_629_, v___y_630_, v___y_631_, v___y_632_,
    );
    lean_dec(v___y_632_);
    lean_dec_ref(v___y_631_);
    lean_dec(v___y_630_);
    lean_dec_ref(v___y_629_);
    lean_dec(v___y_628_);
    lean_dec_ref(v___y_627_);
    lean_dec(v___y_626_);
    lean_dec_ref(v___y_625_);
    lean_dec(v___y_624_);
    return v_res_634_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_tryCatch(
    mut v_f_637_: *mut LeanObject,
    mut v_e_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
    mut v_a_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_652_: u8 = 0;
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut v_unused_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_647_);
                lean_inc_ref(v_a_646_);
                lean_inc(v_a_645_);
                lean_inc_ref(v_a_644_);
                lean_inc(v_a_643_);
                lean_inc_ref(v_a_642_);
                lean_inc(v_a_641_);
                lean_inc_ref(v_a_640_);
                lean_inc(v_a_639_);
                v___x_649_ = lean_apply_11(
                    v_f_637_,
                    v_e_638_,
                    v_a_639_,
                    v_a_640_,
                    v_a_641_,
                    v_a_642_,
                    v_a_643_,
                    v_a_644_,
                    v_a_645_,
                    v_a_646_,
                    v_a_647_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_649_) == 0 {
                    return v___x_649_;
                } else {
                    v_a_650_ = lean_ctor_get(v___x_649_, 0);
                    lean_inc(v_a_650_);
                    v___x_662_ = l_Lean_Exception_isInterrupt(v_a_650_);
                    if v___x_662_ == 0 {
                        v___x_663_ = l_Lean_Exception_isRuntime(v_a_650_);
                        v___y_652_ = v___x_663_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_650_);
                        v___y_652_ = v___x_662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_652_ == 0 {
                    v_isSharedCheck_660_ = (!lean_is_exclusive(v___x_649_)) as u8;
                    if v_isSharedCheck_660_ == 0 {
                        v_unused_661_ = lean_ctor_get(v___x_649_, 0);
                        lean_dec(v_unused_661_);
                        v___x_654_ = v___x_649_;
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_649_);
                        v___x_654_ = lean_box(0);
                        v_isShared_655_ = v_isSharedCheck_660_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_649_;
                }
            }
            2 => {
                v___x_656_ = lean_alloc_ctor(0, 0, (2) as u32);
                lean_ctor_set_uint8(v___x_656_, 0 as u32, v___y_652_);
                lean_ctor_set_uint8(v___x_656_, 1 as u32, v___y_652_);
                if v_isShared_655_ == 0 {
                    lean_ctor_set_tag(v___x_654_, 0);
                    lean_ctor_set(v___x_654_, 0, v___x_656_);
                    v___x_658_ = v___x_654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
                    v___x_658_ = v_reuseFailAlloc_659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Simproc_tryCatch___boxed(
    mut v_f_664_: *mut LeanObject,
    mut v_e_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
    mut v_a_667_: *mut LeanObject,
    mut v_a_668_: *mut LeanObject,
    mut v_a_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
    mut v_a_673_: *mut LeanObject,
    mut v_a_674_: *mut LeanObject,
    mut v_a_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Lean_Meta_Sym_Simp_Simproc_tryCatch(
        v_f_664_, v_e_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_,
        v_a_673_, v_a_674_,
    );
    lean_dec(v_a_674_);
    lean_dec_ref(v_a_673_);
    lean_dec(v_a_672_);
    lean_dec_ref(v_a_671_);
    lean_dec(v_a_670_);
    lean_dec_ref(v_a_669_);
    lean_dec(v_a_668_);
    lean_dec_ref(v_a_667_);
    lean_dec(v_a_666_);
    return v_res_676_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
}
