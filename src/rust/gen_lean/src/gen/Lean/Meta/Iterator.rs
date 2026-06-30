// Lean compiler output
// Module: Lean.Meta.Iterator
// Imports: Lean.Meta.Basic
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_saveState___redArg, runtime_initialize_Lean_Meta_Basic,
};
pub static l_Lean_Meta_Iterator_head___redArg___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 97, 105, 108, 101, 100, 0],
    };
static mut l_Lean_Meta_Iterator_head___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Iterator_head___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Iterator_head___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Iterator_head___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg___lam__0(
    mut v_a_386_: *mut leanh::LeanObject,
    mut v_val_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
    mut v___y_389_: *mut leanh::LeanObject,
    mut v___y_390_: *mut leanh::LeanObject,
    mut v___y_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_420_: u8 = 0;
    let mut v_a_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_428_: u8 = 0;
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_unused_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_435_: u8 = 0;
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_393_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_386_, v___y_389_, v___y_391_);
                if leanh::lean_obj_tag(v___x_393_) == 0 {
                    v_isSharedCheck_430_ = (!leanh::lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v_unused_431_ = leanh::lean_ctor_get(v___x_393_, 0);
                        leanh::lean_dec(v_unused_431_);
                        v___x_395_ = v___x_393_;
                        v_isShared_396_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_393_);
                        v___x_395_ = leanh::lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_432_ = leanh::lean_ctor_get(v___x_393_, 0);
                    v_isSharedCheck_439_ = (!leanh::lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_439_ == 0 {
                        v___x_434_ = v___x_393_;
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_432_);
                        leanh::lean_dec(v___x_393_);
                        v___x_434_ = leanh::lean_box(0);
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_397_ = lean_st_ref_get(v_val_387_);
                if leanh::lean_obj_tag(v___x_397_) == 0 {
                    v___x_398_ = leanh::lean_box(0);
                    if v_isShared_396_ == 0 {
                        leanh::lean_ctor_set(v___x_395_, 0, v___x_398_);
                        v___x_400_ = v___x_395_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
                        v___x_400_ = v_reuseFailAlloc_401_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_395_);
                    v_head_402_ = leanh::lean_ctor_get(v___x_397_, 0);
                    v_tail_403_ = leanh::lean_ctor_get(v___x_397_, 1);
                    v_isSharedCheck_429_ = (!leanh::lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_429_ == 0 {
                        v___x_405_ = v___x_397_;
                        v_isShared_406_ = v_isSharedCheck_429_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_403_);
                        leanh::lean_inc(v_head_402_);
                        leanh::lean_dec(v___x_397_);
                        v___x_405_ = leanh::lean_box(0);
                        v_isShared_406_ = v_isSharedCheck_429_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_400_;
            }
            3 => {
                v___x_407_ = lean_st_ref_set(v_val_387_, v_tail_403_);
                v___x_408_ = l_Lean_Meta_saveState___redArg(v___y_389_, v___y_391_);
                if leanh::lean_obj_tag(v___x_408_) == 0 {
                    v_a_409_ = leanh::lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_420_ = (!leanh::lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_420_ == 0 {
                        v___x_411_ = v___x_408_;
                        v_isShared_412_ = v_isSharedCheck_420_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_409_);
                        leanh::lean_dec(v___x_408_);
                        v___x_411_ = leanh::lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_420_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_405_);
                    leanh::lean_dec(v_head_402_);
                    v_a_421_ = leanh::lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_428_ = (!leanh::lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_428_ == 0 {
                        v___x_423_ = v___x_408_;
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_421_);
                        leanh::lean_dec(v___x_408_);
                        v___x_423_ = leanh::lean_box(0);
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_406_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_405_, 0);
                    leanh::lean_ctor_set(v___x_405_, 1, v_a_409_);
                    v___x_414_ = v___x_405_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_419_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_419_, 0, v_head_402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_409_);
                    v___x_414_ = v_reuseFailAlloc_419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_415_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_415_, 0, v___x_414_);
                if v_isShared_412_ == 0 {
                    leanh::lean_ctor_set(v___x_411_, 0, v___x_415_);
                    v___x_417_ = v___x_411_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
                    v___x_417_ = v_reuseFailAlloc_418_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_417_;
            }
            7 => {
                if v_isShared_424_ == 0 {
                    v___x_426_ = v___x_423_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
                    v___x_426_ = v_reuseFailAlloc_427_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_426_;
            }
            9 => {
                if v_isShared_435_ == 0 {
                    v___x_437_ = v___x_434_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
                    v___x_437_ = v_reuseFailAlloc_438_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed(
    mut v_a_440_: *mut leanh::LeanObject,
    mut v_val_441_: *mut leanh::LeanObject,
    mut v___y_442_: *mut leanh::LeanObject,
    mut v___y_443_: *mut leanh::LeanObject,
    mut v___y_444_: *mut leanh::LeanObject,
    mut v___y_445_: *mut leanh::LeanObject,
    mut v___y_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Meta_Iterator_ofList___redArg___lam__0(
        v_a_440_, v_val_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_,
    );
    leanh::lean_dec(v___y_445_);
    leanh::lean_dec_ref(v___y_444_);
    leanh::lean_dec(v___y_443_);
    leanh::lean_dec_ref(v___y_442_);
    leanh::lean_dec(v_val_441_);
    leanh::lean_dec_ref(v_a_440_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg(
    mut v_l_448_: *mut leanh::LeanObject,
    mut v_a_449_: *mut leanh::LeanObject,
    mut v_a_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_456_: u8 = 0;
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_462_: u8 = 0;
    let mut v_a_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_452_ = l_Lean_Meta_saveState___redArg(v_a_449_, v_a_450_);
                if leanh::lean_obj_tag(v___x_452_) == 0 {
                    v_a_453_ = leanh::lean_ctor_get(v___x_452_, 0);
                    v_isSharedCheck_462_ = (!leanh::lean_is_exclusive(v___x_452_)) as u8;
                    if v_isSharedCheck_462_ == 0 {
                        v___x_455_ = v___x_452_;
                        v_isShared_456_ = v_isSharedCheck_462_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_453_);
                        leanh::lean_dec(v___x_452_);
                        v___x_455_ = leanh::lean_box(0);
                        v_isShared_456_ = v_isSharedCheck_462_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_l_448_);
                    v_a_463_ = leanh::lean_ctor_get(v___x_452_, 0);
                    v_isSharedCheck_470_ = (!leanh::lean_is_exclusive(v___x_452_)) as u8;
                    if v_isSharedCheck_470_ == 0 {
                        v___x_465_ = v___x_452_;
                        v_isShared_466_ = v_isSharedCheck_470_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_463_);
                        leanh::lean_dec(v___x_452_);
                        v___x_465_ = leanh::lean_box(0);
                        v_isShared_466_ = v_isSharedCheck_470_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_457_ = lean_st_mk_ref(v_l_448_);
                v___f_458_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_458_, 0, v_a_453_);
                leanh::lean_closure_set(v___f_458_, 1, v___x_457_);
                if v_isShared_456_ == 0 {
                    leanh::lean_ctor_set(v___x_455_, 0, v___f_458_);
                    v___x_460_ = v___x_455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_461_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_461_, 0, v___f_458_);
                    v___x_460_ = v_reuseFailAlloc_461_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_460_;
            }
            3 => {
                if v_isShared_466_ == 0 {
                    v___x_468_ = v___x_465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
                    v___x_468_ = v_reuseFailAlloc_469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg___boxed(
    mut v_l_471_: *mut leanh::LeanObject,
    mut v_a_472_: *mut leanh::LeanObject,
    mut v_a_473_: *mut leanh::LeanObject,
    mut v_a_474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_475_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_471_, v_a_472_, v_a_473_);
    leanh::lean_dec(v_a_473_);
    leanh::lean_dec(v_a_472_);
    return v_res_475_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList(
    mut v_00_u03b1_476_: *mut leanh::LeanObject,
    mut v_l_477_: *mut leanh::LeanObject,
    mut v_a_478_: *mut leanh::LeanObject,
    mut v_a_479_: *mut leanh::LeanObject,
    mut v_a_480_: *mut leanh::LeanObject,
    mut v_a_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_477_, v_a_479_, v_a_481_);
    return v___x_483_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___boxed(
    mut v_00_u03b1_484_: *mut leanh::LeanObject,
    mut v_l_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_a_489_: *mut leanh::LeanObject,
    mut v_a_490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_Meta_Iterator_ofList(
        v_00_u03b1_484_,
        v_l_485_,
        v_a_486_,
        v_a_487_,
        v_a_488_,
        v_a_489_,
    );
    leanh::lean_dec(v_a_489_);
    leanh::lean_dec_ref(v_a_488_);
    leanh::lean_dec(v_a_487_);
    leanh::lean_dec_ref(v_a_486_);
    return v_res_491_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
    mut v_f_492_: *mut leanh::LeanObject,
    mut v_L_493_: *mut leanh::LeanObject,
    mut v_a_494_: *mut leanh::LeanObject,
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_a_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_536_: u8 = 0;
    let mut v_a_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_544_: u8 = 0;
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut v_a_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_a_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_557_: u8 = 0;
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_isSharedCheck_563_: u8 = 0;
    let mut v_a_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_567_: u8 = 0;
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_L_493_);
                leanh::lean_inc(v_a_497_);
                leanh::lean_inc_ref(v_a_496_);
                leanh::lean_inc(v_a_495_);
                leanh::lean_inc_ref(v_a_494_);
                v___x_499_ = leanh::lean_apply_5(
                    v_L_493_,
                    v_a_494_,
                    v_a_495_,
                    v_a_496_,
                    v_a_497_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_499_) == 0 {
                    v_a_500_ = leanh::lean_ctor_get(v___x_499_, 0);
                    v_isSharedCheck_563_ = (!leanh::lean_is_exclusive(v___x_499_)) as u8;
                    if v_isSharedCheck_563_ == 0 {
                        v___x_502_ = v___x_499_;
                        v_isShared_503_ = v_isSharedCheck_563_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_500_);
                        leanh::lean_dec(v___x_499_);
                        v___x_502_ = leanh::lean_box(0);
                        v_isShared_503_ = v_isSharedCheck_563_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_L_493_);
                    leanh::lean_dec_ref(v_f_492_);
                    v_a_564_ = leanh::lean_ctor_get(v___x_499_, 0);
                    v_isSharedCheck_571_ = (!leanh::lean_is_exclusive(v___x_499_)) as u8;
                    if v_isSharedCheck_571_ == 0 {
                        v___x_566_ = v___x_499_;
                        v_isShared_567_ = v_isSharedCheck_571_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_564_);
                        leanh::lean_dec(v___x_499_);
                        v___x_566_ = leanh::lean_box(0);
                        v_isShared_567_ = v_isSharedCheck_571_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_500_) == 0 {
                    leanh::lean_dec_ref(v_L_493_);
                    leanh::lean_dec_ref(v_f_492_);
                    v___x_504_ = leanh::lean_box(0);
                    if v_isShared_503_ == 0 {
                        leanh::lean_ctor_set(v___x_502_, 0, v___x_504_);
                        v___x_506_ = v___x_502_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_507_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
                        v___x_506_ = v_reuseFailAlloc_507_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_502_);
                    v_val_508_ = leanh::lean_ctor_get(v_a_500_, 0);
                    leanh::lean_inc(v_val_508_);
                    leanh::lean_dec_ref_known(v_a_500_, 1);
                    v_fst_509_ = leanh::lean_ctor_get(v_val_508_, 0);
                    v_snd_510_ = leanh::lean_ctor_get(v_val_508_, 1);
                    v_isSharedCheck_562_ = (!leanh::lean_is_exclusive(v_val_508_)) as u8;
                    if v_isSharedCheck_562_ == 0 {
                        v___x_512_ = v_val_508_;
                        v_isShared_513_ = v_isSharedCheck_562_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_510_);
                        leanh::lean_inc(v_fst_509_);
                        leanh::lean_dec(v_val_508_);
                        v___x_512_ = leanh::lean_box(0);
                        v_isShared_513_ = v_isSharedCheck_562_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_506_;
            }
            3 => {
                v___x_514_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_snd_510_, v_a_495_, v_a_497_);
                leanh::lean_dec(v_snd_510_);
                if leanh::lean_obj_tag(v___x_514_) == 0 {
                    leanh::lean_dec_ref_known(v___x_514_, 1);
                    leanh::lean_inc_ref(v_f_492_);
                    leanh::lean_inc(v_a_497_);
                    leanh::lean_inc_ref(v_a_496_);
                    leanh::lean_inc(v_a_495_);
                    leanh::lean_inc_ref(v_a_494_);
                    v___x_515_ = leanh::lean_apply_6(
                        v_f_492_,
                        v_fst_509_,
                        v_a_494_,
                        v_a_495_,
                        v_a_496_,
                        v_a_497_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_515_) == 0 {
                        v_a_516_ = leanh::lean_ctor_get(v___x_515_, 0);
                        leanh::lean_inc(v_a_516_);
                        leanh::lean_dec_ref_known(v___x_515_, 1);
                        if leanh::lean_obj_tag(v_a_516_) == 0 {
                            leanh::lean_del_object(v___x_512_);
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_L_493_);
                            leanh::lean_dec_ref(v_f_492_);
                            v_val_518_ = leanh::lean_ctor_get(v_a_516_, 0);
                            v_isSharedCheck_545_ =
                                (!leanh::lean_is_exclusive(v_a_516_)) as u8;
                            if v_isSharedCheck_545_ == 0 {
                                v___x_520_ = v_a_516_;
                                v_isShared_521_ = v_isSharedCheck_545_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_518_);
                                leanh::lean_dec(v_a_516_);
                                v___x_520_ = leanh::lean_box(0);
                                v_isShared_521_ = v_isSharedCheck_545_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_512_);
                        leanh::lean_dec_ref(v_L_493_);
                        leanh::lean_dec_ref(v_f_492_);
                        v_a_546_ = leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_553_ = (!leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_553_ == 0 {
                            v___x_548_ = v___x_515_;
                            v_isShared_549_ = v_isSharedCheck_553_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_546_);
                            leanh::lean_dec(v___x_515_);
                            v___x_548_ = leanh::lean_box(0);
                            v_isShared_549_ = v_isSharedCheck_553_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_512_);
                    leanh::lean_dec(v_fst_509_);
                    leanh::lean_dec_ref(v_L_493_);
                    leanh::lean_dec_ref(v_f_492_);
                    v_a_554_ = leanh::lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_561_ = (!leanh::lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_561_ == 0 {
                        v___x_556_ = v___x_514_;
                        v_isShared_557_ = v_isSharedCheck_561_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_554_);
                        leanh::lean_dec(v___x_514_);
                        v___x_556_ = leanh::lean_box(0);
                        v_isShared_557_ = v_isSharedCheck_561_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_522_ = l_Lean_Meta_saveState___redArg(v_a_495_, v_a_497_);
                if leanh::lean_obj_tag(v___x_522_) == 0 {
                    v_a_523_ = leanh::lean_ctor_get(v___x_522_, 0);
                    v_isSharedCheck_536_ = (!leanh::lean_is_exclusive(v___x_522_)) as u8;
                    if v_isSharedCheck_536_ == 0 {
                        v___x_525_ = v___x_522_;
                        v_isShared_526_ = v_isSharedCheck_536_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_523_);
                        leanh::lean_dec(v___x_522_);
                        v___x_525_ = leanh::lean_box(0);
                        v_isShared_526_ = v_isSharedCheck_536_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_520_);
                    leanh::lean_dec(v_val_518_);
                    leanh::lean_del_object(v___x_512_);
                    v_a_537_ = leanh::lean_ctor_get(v___x_522_, 0);
                    v_isSharedCheck_544_ = (!leanh::lean_is_exclusive(v___x_522_)) as u8;
                    if v_isSharedCheck_544_ == 0 {
                        v___x_539_ = v___x_522_;
                        v_isShared_540_ = v_isSharedCheck_544_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_537_);
                        leanh::lean_dec(v___x_522_);
                        v___x_539_ = leanh::lean_box(0);
                        v_isShared_540_ = v_isSharedCheck_544_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_513_ == 0 {
                    leanh::lean_ctor_set(v___x_512_, 1, v_a_523_);
                    leanh::lean_ctor_set(v___x_512_, 0, v_val_518_);
                    v___x_528_ = v___x_512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_523_);
                    v___x_528_ = v_reuseFailAlloc_535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_521_ == 0 {
                    leanh::lean_ctor_set(v___x_520_, 0, v___x_528_);
                    v___x_530_ = v___x_520_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
                    v___x_530_ = v_reuseFailAlloc_534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_526_ == 0 {
                    leanh::lean_ctor_set(v___x_525_, 0, v___x_530_);
                    v___x_532_ = v___x_525_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
                    v___x_532_ = v_reuseFailAlloc_533_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_532_;
            }
            9 => {
                if v_isShared_540_ == 0 {
                    v___x_542_ = v___x_539_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_543_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
                    v___x_542_ = v_reuseFailAlloc_543_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_542_;
            }
            11 => {
                if v_isShared_549_ == 0 {
                    v___x_551_ = v___x_548_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
                    v___x_551_ = v_reuseFailAlloc_552_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_551_;
            }
            13 => {
                if v_isShared_557_ == 0 {
                    v___x_559_ = v___x_556_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
                    v___x_559_ = v_reuseFailAlloc_560_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_559_;
            }
            15 => {
                if v_isShared_567_ == 0 {
                    v___x_569_ = v___x_566_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
                    v___x_569_ = v_reuseFailAlloc_570_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg___boxed(
    mut v_f_572_: *mut leanh::LeanObject,
    mut v_L_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
    mut v_a_575_: *mut leanh::LeanObject,
    mut v_a_576_: *mut leanh::LeanObject,
    mut v_a_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
        v_f_572_, v_L_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_,
    );
    leanh::lean_dec(v_a_577_);
    leanh::lean_dec_ref(v_a_576_);
    leanh::lean_dec(v_a_575_);
    leanh::lean_dec_ref(v_a_574_);
    return v_res_579_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(
    mut v_00_u03b1_580_: *mut leanh::LeanObject,
    mut v_00_u03b2_581_: *mut leanh::LeanObject,
    mut v_f_582_: *mut leanh::LeanObject,
    mut v_L_583_: *mut leanh::LeanObject,
    mut v_a_584_: *mut leanh::LeanObject,
    mut v_a_585_: *mut leanh::LeanObject,
    mut v_a_586_: *mut leanh::LeanObject,
    mut v_a_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
        v_f_582_, v_L_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_,
    );
    return v___x_589_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(
    mut v_00_u03b1_590_: *mut leanh::LeanObject,
    mut v_00_u03b2_591_: *mut leanh::LeanObject,
    mut v_f_592_: *mut leanh::LeanObject,
    mut v_L_593_: *mut leanh::LeanObject,
    mut v_a_594_: *mut leanh::LeanObject,
    mut v_a_595_: *mut leanh::LeanObject,
    mut v_a_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(
        v_00_u03b1_590_,
        v_00_u03b2_591_,
        v_f_592_,
        v_L_593_,
        v_a_594_,
        v_a_595_,
        v_a_596_,
        v_a_597_,
    );
    leanh::lean_dec(v_a_597_);
    leanh::lean_dec_ref(v_a_596_);
    leanh::lean_dec(v_a_595_);
    leanh::lean_dec_ref(v_a_594_);
    return v_res_599_;
}
pub unsafe fn l_Lean_Meta_Iterator_filterMapM___redArg(
    mut v_f_600_: *mut leanh::LeanObject,
    mut v_L_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_602_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_602_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_602_, 2, v_f_600_);
    leanh::lean_closure_set(v___x_602_, 3, v_L_601_);
    return v___x_602_;
}
pub unsafe fn l_Lean_Meta_Iterator_filterMapM(
    mut v_00_u03b1_603_: *mut leanh::LeanObject,
    mut v_00_u03b2_604_: *mut leanh::LeanObject,
    mut v_f_605_: *mut leanh::LeanObject,
    mut v_L_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_607_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_607_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_607_, 2, v_f_605_);
    leanh::lean_closure_set(v___x_607_, 3, v_L_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(
    mut v_msgData_608_: *mut leanh::LeanObject,
    mut v___y_609_: *mut leanh::LeanObject,
    mut v___y_610_: *mut leanh::LeanObject,
    mut v___y_611_: *mut leanh::LeanObject,
    mut v___y_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_st_ref_get(v___y_612_);
    v_env_615_ = leanh::lean_ctor_get(v___x_614_, 0);
    leanh::lean_inc_ref(v_env_615_);
    leanh::lean_dec(v___x_614_);
    v___x_616_ = lean_st_ref_get(v___y_610_);
    v_mctx_617_ = leanh::lean_ctor_get(v___x_616_, 0);
    leanh::lean_inc_ref(v_mctx_617_);
    leanh::lean_dec(v___x_616_);
    v_lctx_618_ = leanh::lean_ctor_get(v___y_609_, 2);
    v_options_619_ = leanh::lean_ctor_get(v___y_611_, 2);
    leanh::lean_inc_ref(v_options_619_);
    leanh::lean_inc_ref(v_lctx_618_);
    v___x_620_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_620_, 0, v_env_615_);
    leanh::lean_ctor_set(v___x_620_, 1, v_mctx_617_);
    leanh::lean_ctor_set(v___x_620_, 2, v_lctx_618_);
    leanh::lean_ctor_set(v___x_620_, 3, v_options_619_);
    v___x_621_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_621_, 0, v___x_620_);
    leanh::lean_ctor_set(v___x_621_, 1, v_msgData_608_);
    v___x_622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_622_, 0, v___x_621_);
    return v___x_622_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0___boxed(
    mut v_msgData_623_: *mut leanh::LeanObject,
    mut v___y_624_: *mut leanh::LeanObject,
    mut v___y_625_: *mut leanh::LeanObject,
    mut v___y_626_: *mut leanh::LeanObject,
    mut v___y_627_: *mut leanh::LeanObject,
    mut v___y_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msgData_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
    leanh::lean_dec(v___y_627_);
    leanh::lean_dec_ref(v___y_626_);
    leanh::lean_dec(v___y_625_);
    leanh::lean_dec_ref(v___y_624_);
    return v_res_629_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
    mut v_msg_630_: *mut leanh::LeanObject,
    mut v___y_631_: *mut leanh::LeanObject,
    mut v___y_632_: *mut leanh::LeanObject,
    mut v___y_633_: *mut leanh::LeanObject,
    mut v___y_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_636_ = leanh::lean_ctor_get(v___y_633_, 5);
                v___x_637_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
                v_a_638_ = leanh::lean_ctor_get(v___x_637_, 0);
                v_isSharedCheck_646_ = (!leanh::lean_is_exclusive(v___x_637_)) as u8;
                if v_isSharedCheck_646_ == 0 {
                    v___x_640_ = v___x_637_;
                    v_isShared_641_ = v_isSharedCheck_646_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_638_);
                    leanh::lean_dec(v___x_637_);
                    v___x_640_ = leanh::lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_646_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_636_);
                v___x_642_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_642_, 0, v_ref_636_);
                leanh::lean_ctor_set(v___x_642_, 1, v_a_638_);
                if v_isShared_641_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_640_, 1);
                    leanh::lean_ctor_set(v___x_640_, 0, v___x_642_);
                    v___x_644_ = v___x_640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
                    v___x_644_ = v_reuseFailAlloc_645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg___boxed(
    mut v_msg_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
    mut v___y_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
    mut v___y_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
        v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_,
    );
    leanh::lean_dec(v___y_651_);
    leanh::lean_dec_ref(v___y_650_);
    leanh::lean_dec(v___y_649_);
    leanh::lean_dec_ref(v___y_648_);
    return v_res_653_;
}
pub unsafe fn _init_l_Lean_Meta_Iterator_head___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Iterator_head___redArg___closed__0;
    v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
    return v___x_656_;
}
pub unsafe fn l_Lean_Meta_Iterator_head___redArg(
    mut v_L_657_: *mut leanh::LeanObject,
    mut v_a_658_: *mut leanh::LeanObject,
    mut v_a_659_: *mut leanh::LeanObject,
    mut v_a_660_: *mut leanh::LeanObject,
    mut v_a_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut v_unused_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_682_: u8 = 0;
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_686_: u8 = 0;
    let mut v_a_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_661_);
                leanh::lean_inc_ref(v_a_660_);
                leanh::lean_inc(v_a_659_);
                leanh::lean_inc_ref(v_a_658_);
                v___x_663_ = leanh::lean_apply_5(
                    v_L_657_,
                    v_a_658_,
                    v_a_659_,
                    v_a_660_,
                    v_a_661_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_663_) == 0 {
                    v_a_664_ = leanh::lean_ctor_get(v___x_663_, 0);
                    leanh::lean_inc(v_a_664_);
                    leanh::lean_dec_ref_known(v___x_663_, 1);
                    if leanh::lean_obj_tag(v_a_664_) == 0 {
                        v___x_665_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Iterator_head___redArg___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Iterator_head___redArg___closed__1_once
                            ),
                            _init_l_Lean_Meta_Iterator_head___redArg___closed__1,
                        );
                        v___x_666_ =
                            l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
                                v___x_665_, v_a_658_, v_a_659_, v_a_660_, v_a_661_,
                            );
                        return v___x_666_;
                    } else {
                        v_val_667_ = leanh::lean_ctor_get(v_a_664_, 0);
                        leanh::lean_inc(v_val_667_);
                        leanh::lean_dec_ref_known(v_a_664_, 1);
                        v_fst_668_ = leanh::lean_ctor_get(v_val_667_, 0);
                        leanh::lean_inc(v_fst_668_);
                        v_snd_669_ = leanh::lean_ctor_get(v_val_667_, 1);
                        leanh::lean_inc(v_snd_669_);
                        leanh::lean_dec(v_val_667_);
                        v___x_670_ =
                            l_Lean_Meta_SavedState_restore___redArg(v_snd_669_, v_a_659_, v_a_661_);
                        leanh::lean_dec(v_snd_669_);
                        if leanh::lean_obj_tag(v___x_670_) == 0 {
                            v_isSharedCheck_677_ =
                                (!leanh::lean_is_exclusive(v___x_670_)) as u8;
                            if v_isSharedCheck_677_ == 0 {
                                v_unused_678_ = leanh::lean_ctor_get(v___x_670_, 0);
                                leanh::lean_dec(v_unused_678_);
                                v___x_672_ = v___x_670_;
                                v_isShared_673_ = v_isSharedCheck_677_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_670_);
                                v___x_672_ = leanh::lean_box(0);
                                v_isShared_673_ = v_isSharedCheck_677_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_668_);
                            v_a_679_ = leanh::lean_ctor_get(v___x_670_, 0);
                            v_isSharedCheck_686_ =
                                (!leanh::lean_is_exclusive(v___x_670_)) as u8;
                            if v_isSharedCheck_686_ == 0 {
                                v___x_681_ = v___x_670_;
                                v_isShared_682_ = v_isSharedCheck_686_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_679_);
                                leanh::lean_dec(v___x_670_);
                                v___x_681_ = leanh::lean_box(0);
                                v_isShared_682_ = v_isSharedCheck_686_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_687_ = leanh::lean_ctor_get(v___x_663_, 0);
                    v_isSharedCheck_694_ = (!leanh::lean_is_exclusive(v___x_663_)) as u8;
                    if v_isSharedCheck_694_ == 0 {
                        v___x_689_ = v___x_663_;
                        v_isShared_690_ = v_isSharedCheck_694_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_687_);
                        leanh::lean_dec(v___x_663_);
                        v___x_689_ = leanh::lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_694_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_673_ == 0 {
                    leanh::lean_ctor_set(v___x_672_, 0, v_fst_668_);
                    v___x_675_ = v___x_672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_668_);
                    v___x_675_ = v_reuseFailAlloc_676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_675_;
            }
            3 => {
                if v_isShared_682_ == 0 {
                    v___x_684_ = v___x_681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_685_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
                    v___x_684_ = v_reuseFailAlloc_685_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_684_;
            }
            5 => {
                if v_isShared_690_ == 0 {
                    v___x_692_ = v___x_689_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
                    v___x_692_ = v_reuseFailAlloc_693_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Iterator_head___redArg___boxed(
    mut v_L_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
    mut v_a_697_: *mut leanh::LeanObject,
    mut v_a_698_: *mut leanh::LeanObject,
    mut v_a_699_: *mut leanh::LeanObject,
    mut v_a_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ =
        l_Lean_Meta_Iterator_head___redArg(v_L_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
    leanh::lean_dec(v_a_699_);
    leanh::lean_dec_ref(v_a_698_);
    leanh::lean_dec(v_a_697_);
    leanh::lean_dec_ref(v_a_696_);
    return v_res_701_;
}
pub unsafe fn l_Lean_Meta_Iterator_head(
    mut v_00_u03b1_702_: *mut leanh::LeanObject,
    mut v_L_703_: *mut leanh::LeanObject,
    mut v_a_704_: *mut leanh::LeanObject,
    mut v_a_705_: *mut leanh::LeanObject,
    mut v_a_706_: *mut leanh::LeanObject,
    mut v_a_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ =
        l_Lean_Meta_Iterator_head___redArg(v_L_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
    return v___x_709_;
}
pub unsafe fn l_Lean_Meta_Iterator_head___boxed(
    mut v_00_u03b1_710_: *mut leanh::LeanObject,
    mut v_L_711_: *mut leanh::LeanObject,
    mut v_a_712_: *mut leanh::LeanObject,
    mut v_a_713_: *mut leanh::LeanObject,
    mut v_a_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
    mut v_a_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Meta_Iterator_head(
        v_00_u03b1_710_,
        v_L_711_,
        v_a_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
    );
    leanh::lean_dec(v_a_715_);
    leanh::lean_dec_ref(v_a_714_);
    leanh::lean_dec(v_a_713_);
    leanh::lean_dec_ref(v_a_712_);
    return v_res_717_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(
    mut v_00_u03b1_718_: *mut leanh::LeanObject,
    mut v_msg_719_: *mut leanh::LeanObject,
    mut v___y_720_: *mut leanh::LeanObject,
    mut v___y_721_: *mut leanh::LeanObject,
    mut v___y_722_: *mut leanh::LeanObject,
    mut v___y_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
        v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_,
    );
    return v___x_725_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___boxed(
    mut v_00_u03b1_726_: *mut leanh::LeanObject,
    mut v_msg_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(
        v_00_u03b1_726_,
        v_msg_727_,
        v___y_728_,
        v___y_729_,
        v___y_730_,
        v___y_731_,
    );
    leanh::lean_dec(v___y_731_);
    leanh::lean_dec_ref(v___y_730_);
    leanh::lean_dec(v___y_729_);
    leanh::lean_dec_ref(v___y_728_);
    return v_res_733_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___redArg(
    mut v_L_734_: *mut leanh::LeanObject,
    mut v_f_735_: *mut leanh::LeanObject,
    mut v_a_736_: *mut leanh::LeanObject,
    mut v_a_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
    mut v_a_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___x_741_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_741_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_741_, 2, v_f_735_);
    leanh::lean_closure_set(v___x_741_, 3, v_L_734_);
    v___x_742_ =
        l_Lean_Meta_Iterator_head___redArg(v___x_741_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
    return v___x_742_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___redArg___boxed(
    mut v_L_743_: *mut leanh::LeanObject,
    mut v_f_744_: *mut leanh::LeanObject,
    mut v_a_745_: *mut leanh::LeanObject,
    mut v_a_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
    mut v_a_749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Lean_Meta_Iterator_firstM___redArg(
        v_L_743_, v_f_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_,
    );
    leanh::lean_dec(v_a_748_);
    leanh::lean_dec_ref(v_a_747_);
    leanh::lean_dec(v_a_746_);
    leanh::lean_dec_ref(v_a_745_);
    return v_res_750_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM(
    mut v_00_u03b1_751_: *mut leanh::LeanObject,
    mut v_00_u03b2_752_: *mut leanh::LeanObject,
    mut v_L_753_: *mut leanh::LeanObject,
    mut v_f_754_: *mut leanh::LeanObject,
    mut v_a_755_: *mut leanh::LeanObject,
    mut v_a_756_: *mut leanh::LeanObject,
    mut v_a_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Lean_Meta_Iterator_firstM___redArg(
        v_L_753_, v_f_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_,
    );
    return v___x_760_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___boxed(
    mut v_00_u03b1_761_: *mut leanh::LeanObject,
    mut v_00_u03b2_762_: *mut leanh::LeanObject,
    mut v_L_763_: *mut leanh::LeanObject,
    mut v_f_764_: *mut leanh::LeanObject,
    mut v_a_765_: *mut leanh::LeanObject,
    mut v_a_766_: *mut leanh::LeanObject,
    mut v_a_767_: *mut leanh::LeanObject,
    mut v_a_768_: *mut leanh::LeanObject,
    mut v_a_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Lean_Meta_Iterator_firstM(
        v_00_u03b1_761_,
        v_00_u03b2_762_,
        v_L_763_,
        v_f_764_,
        v_a_765_,
        v_a_766_,
        v_a_767_,
        v_a_768_,
    );
    leanh::lean_dec(v_a_768_);
    leanh::lean_dec_ref(v_a_767_);
    leanh::lean_dec(v_a_766_);
    leanh::lean_dec_ref(v_a_765_);
    return v_res_770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Iterator(builtin);
}