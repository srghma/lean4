// Lean compiler output
// Module: Lean.Meta.Iterator
// Imports: Lean.Meta.Basic
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_saveState___redArg, runtime_initialize_Lean_Meta_Basic,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
};
pub static l_Lean_Meta_Iterator_head___redArg___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Iterator_head___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Iterator_head___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Iterator_head___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Iterator_head___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg___lam__0(
    mut v_a_386_: *mut LeanObject,
    mut v_val_387_: *mut LeanObject,
    mut v___y_388_: *mut LeanObject,
    mut v___y_389_: *mut LeanObject,
    mut v___y_390_: *mut LeanObject,
    mut v___y_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_420_: u8 = 0;
    let mut v_a_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_428_: u8 = 0;
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut v_unused_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_435_: u8 = 0;
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_393_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_386_, v___y_389_, v___y_391_);
                if lean_obj_tag(v___x_393_) == 0 {
                    v_isSharedCheck_430_ = (!lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v_unused_431_ = lean_ctor_get(v___x_393_, 0);
                        lean_dec(v_unused_431_);
                        v___x_395_ = v___x_393_;
                        v_isShared_396_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_393_);
                        v___x_395_ = lean_box(0);
                        v_isShared_396_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_432_ = lean_ctor_get(v___x_393_, 0);
                    v_isSharedCheck_439_ = (!lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_439_ == 0 {
                        v___x_434_ = v___x_393_;
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_432_);
                        lean_dec(v___x_393_);
                        v___x_434_ = lean_box(0);
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_397_ = lean_st_ref_get(v_val_387_);
                if lean_obj_tag(v___x_397_) == 0 {
                    v___x_398_ = lean_box(0);
                    if v_isShared_396_ == 0 {
                        lean_ctor_set(v___x_395_, 0, v___x_398_);
                        v___x_400_ = v___x_395_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
                        v___x_400_ = v_reuseFailAlloc_401_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_395_);
                    v_head_402_ = lean_ctor_get(v___x_397_, 0);
                    v_tail_403_ = lean_ctor_get(v___x_397_, 1);
                    v_isSharedCheck_429_ = (!lean_is_exclusive(v___x_397_)) as u8;
                    if v_isSharedCheck_429_ == 0 {
                        v___x_405_ = v___x_397_;
                        v_isShared_406_ = v_isSharedCheck_429_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_tail_403_);
                        lean_inc(v_head_402_);
                        lean_dec(v___x_397_);
                        v___x_405_ = lean_box(0);
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
                if lean_obj_tag(v___x_408_) == 0 {
                    v_a_409_ = lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_420_ = (!lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_420_ == 0 {
                        v___x_411_ = v___x_408_;
                        v_isShared_412_ = v_isSharedCheck_420_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_409_);
                        lean_dec(v___x_408_);
                        v___x_411_ = lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_420_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_405_);
                    lean_dec(v_head_402_);
                    v_a_421_ = lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_428_ = (!lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_428_ == 0 {
                        v___x_423_ = v___x_408_;
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_421_);
                        lean_dec(v___x_408_);
                        v___x_423_ = lean_box(0);
                        v_isShared_424_ = v_isSharedCheck_428_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_406_ == 0 {
                    lean_ctor_set_tag(v___x_405_, 0);
                    lean_ctor_set(v___x_405_, 1, v_a_409_);
                    v___x_414_ = v___x_405_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_419_, 0, v_head_402_);
                    lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_409_);
                    v___x_414_ = v_reuseFailAlloc_419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_415_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_415_, 0, v___x_414_);
                if v_isShared_412_ == 0 {
                    lean_ctor_set(v___x_411_, 0, v___x_415_);
                    v___x_417_ = v___x_411_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
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
                    v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
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
                    v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
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
    mut v_a_440_: *mut LeanObject,
    mut v_val_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Meta_Iterator_ofList___redArg___lam__0(
        v_a_440_, v_val_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_,
    );
    lean_dec(v___y_445_);
    lean_dec_ref(v___y_444_);
    lean_dec(v___y_443_);
    lean_dec_ref(v___y_442_);
    lean_dec(v_val_441_);
    lean_dec_ref(v_a_440_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___redArg(
    mut v_l_448_: *mut LeanObject,
    mut v_a_449_: *mut LeanObject,
    mut v_a_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_456_: u8 = 0;
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_462_: u8 = 0;
    let mut v_a_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_452_ = l_Lean_Meta_saveState___redArg(v_a_449_, v_a_450_);
                if lean_obj_tag(v___x_452_) == 0 {
                    v_a_453_ = lean_ctor_get(v___x_452_, 0);
                    v_isSharedCheck_462_ = (!lean_is_exclusive(v___x_452_)) as u8;
                    if v_isSharedCheck_462_ == 0 {
                        v___x_455_ = v___x_452_;
                        v_isShared_456_ = v_isSharedCheck_462_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_453_);
                        lean_dec(v___x_452_);
                        v___x_455_ = lean_box(0);
                        v_isShared_456_ = v_isSharedCheck_462_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_l_448_);
                    v_a_463_ = lean_ctor_get(v___x_452_, 0);
                    v_isSharedCheck_470_ = (!lean_is_exclusive(v___x_452_)) as u8;
                    if v_isSharedCheck_470_ == 0 {
                        v___x_465_ = v___x_452_;
                        v_isShared_466_ = v_isSharedCheck_470_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_463_);
                        lean_dec(v___x_452_);
                        v___x_465_ = lean_box(0);
                        v_isShared_466_ = v_isSharedCheck_470_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_457_ = lean_st_mk_ref(v_l_448_);
                v___f_458_ = lean_alloc_closure(
                    l_Lean_Meta_Iterator_ofList___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_458_, 0, v_a_453_);
                lean_closure_set(v___f_458_, 1, v___x_457_);
                if v_isShared_456_ == 0 {
                    lean_ctor_set(v___x_455_, 0, v___f_458_);
                    v___x_460_ = v___x_455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_461_, 0, v___f_458_);
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
                    v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
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
    mut v_l_471_: *mut LeanObject,
    mut v_a_472_: *mut LeanObject,
    mut v_a_473_: *mut LeanObject,
    mut v_a_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_475_: *mut LeanObject = core::ptr::null_mut();
    v_res_475_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_471_, v_a_472_, v_a_473_);
    lean_dec(v_a_473_);
    lean_dec(v_a_472_);
    return v_res_475_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList(
    mut v_00_u03b1_476_: *mut LeanObject,
    mut v_l_477_: *mut LeanObject,
    mut v_a_478_: *mut LeanObject,
    mut v_a_479_: *mut LeanObject,
    mut v_a_480_: *mut LeanObject,
    mut v_a_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Lean_Meta_Iterator_ofList___redArg(v_l_477_, v_a_479_, v_a_481_);
    return v___x_483_;
}
pub unsafe fn l_Lean_Meta_Iterator_ofList___boxed(
    mut v_00_u03b1_484_: *mut LeanObject,
    mut v_l_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
    mut v_a_489_: *mut LeanObject,
    mut v_a_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_491_: *mut LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_Meta_Iterator_ofList(
        v_00_u03b1_484_,
        v_l_485_,
        v_a_486_,
        v_a_487_,
        v_a_488_,
        v_a_489_,
    );
    lean_dec(v_a_489_);
    lean_dec_ref(v_a_488_);
    lean_dec(v_a_487_);
    lean_dec_ref(v_a_486_);
    return v_res_491_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
    mut v_f_492_: *mut LeanObject,
    mut v_L_493_: *mut LeanObject,
    mut v_a_494_: *mut LeanObject,
    mut v_a_495_: *mut LeanObject,
    mut v_a_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_503_: u8 = 0;
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_536_: u8 = 0;
    let mut v_a_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_544_: u8 = 0;
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_553_: u8 = 0;
    let mut v_a_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_557_: u8 = 0;
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_isSharedCheck_563_: u8 = 0;
    let mut v_a_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_567_: u8 = 0;
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_L_493_);
                lean_inc(v_a_497_);
                lean_inc_ref(v_a_496_);
                lean_inc(v_a_495_);
                lean_inc_ref(v_a_494_);
                v___x_499_ = lean_apply_5(
                    v_L_493_,
                    v_a_494_,
                    v_a_495_,
                    v_a_496_,
                    v_a_497_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_499_) == 0 {
                    v_a_500_ = lean_ctor_get(v___x_499_, 0);
                    v_isSharedCheck_563_ = (!lean_is_exclusive(v___x_499_)) as u8;
                    if v_isSharedCheck_563_ == 0 {
                        v___x_502_ = v___x_499_;
                        v_isShared_503_ = v_isSharedCheck_563_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_500_);
                        lean_dec(v___x_499_);
                        v___x_502_ = lean_box(0);
                        v_isShared_503_ = v_isSharedCheck_563_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_L_493_);
                    lean_dec_ref(v_f_492_);
                    v_a_564_ = lean_ctor_get(v___x_499_, 0);
                    v_isSharedCheck_571_ = (!lean_is_exclusive(v___x_499_)) as u8;
                    if v_isSharedCheck_571_ == 0 {
                        v___x_566_ = v___x_499_;
                        v_isShared_567_ = v_isSharedCheck_571_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_564_);
                        lean_dec(v___x_499_);
                        v___x_566_ = lean_box(0);
                        v_isShared_567_ = v_isSharedCheck_571_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_500_) == 0 {
                    lean_dec_ref(v_L_493_);
                    lean_dec_ref(v_f_492_);
                    v___x_504_ = lean_box(0);
                    if v_isShared_503_ == 0 {
                        lean_ctor_set(v___x_502_, 0, v___x_504_);
                        v___x_506_ = v___x_502_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
                        v___x_506_ = v_reuseFailAlloc_507_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_502_);
                    v_val_508_ = lean_ctor_get(v_a_500_, 0);
                    lean_inc(v_val_508_);
                    lean_dec_ref_known(v_a_500_, 1);
                    v_fst_509_ = lean_ctor_get(v_val_508_, 0);
                    v_snd_510_ = lean_ctor_get(v_val_508_, 1);
                    v_isSharedCheck_562_ = (!lean_is_exclusive(v_val_508_)) as u8;
                    if v_isSharedCheck_562_ == 0 {
                        v___x_512_ = v_val_508_;
                        v_isShared_513_ = v_isSharedCheck_562_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_510_);
                        lean_inc(v_fst_509_);
                        lean_dec(v_val_508_);
                        v___x_512_ = lean_box(0);
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
                lean_dec(v_snd_510_);
                if lean_obj_tag(v___x_514_) == 0 {
                    lean_dec_ref_known(v___x_514_, 1);
                    lean_inc_ref(v_f_492_);
                    lean_inc(v_a_497_);
                    lean_inc_ref(v_a_496_);
                    lean_inc(v_a_495_);
                    lean_inc_ref(v_a_494_);
                    v___x_515_ = lean_apply_6(
                        v_f_492_,
                        v_fst_509_,
                        v_a_494_,
                        v_a_495_,
                        v_a_496_,
                        v_a_497_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_515_) == 0 {
                        v_a_516_ = lean_ctor_get(v___x_515_, 0);
                        lean_inc(v_a_516_);
                        lean_dec_ref_known(v___x_515_, 1);
                        if lean_obj_tag(v_a_516_) == 0 {
                            lean_del_object(v___x_512_);
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_L_493_);
                            lean_dec_ref(v_f_492_);
                            v_val_518_ = lean_ctor_get(v_a_516_, 0);
                            v_isSharedCheck_545_ = (!lean_is_exclusive(v_a_516_)) as u8;
                            if v_isSharedCheck_545_ == 0 {
                                v___x_520_ = v_a_516_;
                                v_isShared_521_ = v_isSharedCheck_545_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_val_518_);
                                lean_dec(v_a_516_);
                                v___x_520_ = lean_box(0);
                                v_isShared_521_ = v_isSharedCheck_545_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_512_);
                        lean_dec_ref(v_L_493_);
                        lean_dec_ref(v_f_492_);
                        v_a_546_ = lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_553_ = (!lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_553_ == 0 {
                            v___x_548_ = v___x_515_;
                            v_isShared_549_ = v_isSharedCheck_553_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_546_);
                            lean_dec(v___x_515_);
                            v___x_548_ = lean_box(0);
                            v_isShared_549_ = v_isSharedCheck_553_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_512_);
                    lean_dec(v_fst_509_);
                    lean_dec_ref(v_L_493_);
                    lean_dec_ref(v_f_492_);
                    v_a_554_ = lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_561_ = (!lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_561_ == 0 {
                        v___x_556_ = v___x_514_;
                        v_isShared_557_ = v_isSharedCheck_561_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_554_);
                        lean_dec(v___x_514_);
                        v___x_556_ = lean_box(0);
                        v_isShared_557_ = v_isSharedCheck_561_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_522_ = l_Lean_Meta_saveState___redArg(v_a_495_, v_a_497_);
                if lean_obj_tag(v___x_522_) == 0 {
                    v_a_523_ = lean_ctor_get(v___x_522_, 0);
                    v_isSharedCheck_536_ = (!lean_is_exclusive(v___x_522_)) as u8;
                    if v_isSharedCheck_536_ == 0 {
                        v___x_525_ = v___x_522_;
                        v_isShared_526_ = v_isSharedCheck_536_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_523_);
                        lean_dec(v___x_522_);
                        v___x_525_ = lean_box(0);
                        v_isShared_526_ = v_isSharedCheck_536_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_520_);
                    lean_dec(v_val_518_);
                    lean_del_object(v___x_512_);
                    v_a_537_ = lean_ctor_get(v___x_522_, 0);
                    v_isSharedCheck_544_ = (!lean_is_exclusive(v___x_522_)) as u8;
                    if v_isSharedCheck_544_ == 0 {
                        v___x_539_ = v___x_522_;
                        v_isShared_540_ = v_isSharedCheck_544_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_537_);
                        lean_dec(v___x_522_);
                        v___x_539_ = lean_box(0);
                        v_isShared_540_ = v_isSharedCheck_544_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_513_ == 0 {
                    lean_ctor_set(v___x_512_, 1, v_a_523_);
                    lean_ctor_set(v___x_512_, 0, v_val_518_);
                    v___x_528_ = v___x_512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_518_);
                    lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_523_);
                    v___x_528_ = v_reuseFailAlloc_535_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_521_ == 0 {
                    lean_ctor_set(v___x_520_, 0, v___x_528_);
                    v___x_530_ = v___x_520_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
                    v___x_530_ = v_reuseFailAlloc_534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_526_ == 0 {
                    lean_ctor_set(v___x_525_, 0, v___x_530_);
                    v___x_532_ = v___x_525_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
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
                    v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
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
                    v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
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
                    v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
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
                    v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
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
    mut v_f_572_: *mut LeanObject,
    mut v_L_573_: *mut LeanObject,
    mut v_a_574_: *mut LeanObject,
    mut v_a_575_: *mut LeanObject,
    mut v_a_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_579_: *mut LeanObject = core::ptr::null_mut();
    v_res_579_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
        v_f_572_, v_L_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_,
    );
    lean_dec(v_a_577_);
    lean_dec_ref(v_a_576_);
    lean_dec(v_a_575_);
    lean_dec_ref(v_a_574_);
    return v_res_579_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next(
    mut v_00_u03b1_580_: *mut LeanObject,
    mut v_00_u03b2_581_: *mut LeanObject,
    mut v_f_582_: *mut LeanObject,
    mut v_L_583_: *mut LeanObject,
    mut v_a_584_: *mut LeanObject,
    mut v_a_585_: *mut LeanObject,
    mut v_a_586_: *mut LeanObject,
    mut v_a_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_589_ = l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___redArg(
        v_f_582_, v_L_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_,
    );
    return v___x_589_;
}
pub unsafe fn l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed(
    mut v_00_u03b1_590_: *mut LeanObject,
    mut v_00_u03b2_591_: *mut LeanObject,
    mut v_f_592_: *mut LeanObject,
    mut v_L_593_: *mut LeanObject,
    mut v_a_594_: *mut LeanObject,
    mut v_a_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_599_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_597_);
    lean_dec_ref(v_a_596_);
    lean_dec(v_a_595_);
    lean_dec_ref(v_a_594_);
    return v_res_599_;
}
pub unsafe fn l_Lean_Meta_Iterator_filterMapM___redArg(
    mut v_f_600_: *mut LeanObject,
    mut v_L_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_602_ = lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_602_, 0, lean_box(0));
    lean_closure_set(v___x_602_, 1, lean_box(0));
    lean_closure_set(v___x_602_, 2, v_f_600_);
    lean_closure_set(v___x_602_, 3, v_L_601_);
    return v___x_602_;
}
pub unsafe fn l_Lean_Meta_Iterator_filterMapM(
    mut v_00_u03b1_603_: *mut LeanObject,
    mut v_00_u03b2_604_: *mut LeanObject,
    mut v_f_605_: *mut LeanObject,
    mut v_L_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_607_ = lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_607_, 0, lean_box(0));
    lean_closure_set(v___x_607_, 1, lean_box(0));
    lean_closure_set(v___x_607_, 2, v_f_605_);
    lean_closure_set(v___x_607_, 3, v_L_606_);
    return v___x_607_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(
    mut v_msgData_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
    mut v___y_610_: *mut LeanObject,
    mut v___y_611_: *mut LeanObject,
    mut v___y_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_st_ref_get(v___y_612_);
    v_env_615_ = lean_ctor_get(v___x_614_, 0);
    lean_inc_ref(v_env_615_);
    lean_dec(v___x_614_);
    v___x_616_ = lean_st_ref_get(v___y_610_);
    v_mctx_617_ = lean_ctor_get(v___x_616_, 0);
    lean_inc_ref(v_mctx_617_);
    lean_dec(v___x_616_);
    v_lctx_618_ = lean_ctor_get(v___y_609_, 2);
    v_options_619_ = lean_ctor_get(v___y_611_, 2);
    lean_inc_ref(v_options_619_);
    lean_inc_ref(v_lctx_618_);
    v___x_620_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_620_, 0, v_env_615_);
    lean_ctor_set(v___x_620_, 1, v_mctx_617_);
    lean_ctor_set(v___x_620_, 2, v_lctx_618_);
    lean_ctor_set(v___x_620_, 3, v_options_619_);
    v___x_621_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_621_, 0, v___x_620_);
    lean_ctor_set(v___x_621_, 1, v_msgData_608_);
    v___x_622_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_622_, 0, v___x_621_);
    return v___x_622_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0___boxed(
    mut v_msgData_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
    mut v___y_625_: *mut LeanObject,
    mut v___y_626_: *mut LeanObject,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_629_: *mut LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msgData_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
    lean_dec(v___y_627_);
    lean_dec_ref(v___y_626_);
    lean_dec(v___y_625_);
    lean_dec_ref(v___y_624_);
    return v_res_629_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
    mut v_msg_630_: *mut LeanObject,
    mut v___y_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_636_ = lean_ctor_get(v___y_633_, 5);
                v___x_637_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0_spec__0(v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
                v_a_638_ = lean_ctor_get(v___x_637_, 0);
                v_isSharedCheck_646_ = (!lean_is_exclusive(v___x_637_)) as u8;
                if v_isSharedCheck_646_ == 0 {
                    v___x_640_ = v___x_637_;
                    v_isShared_641_ = v_isSharedCheck_646_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_638_);
                    lean_dec(v___x_637_);
                    v___x_640_ = lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_646_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_636_);
                v___x_642_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_642_, 0, v_ref_636_);
                lean_ctor_set(v___x_642_, 1, v_a_638_);
                if v_isShared_641_ == 0 {
                    lean_ctor_set_tag(v___x_640_, 1);
                    lean_ctor_set(v___x_640_, 0, v___x_642_);
                    v___x_644_ = v___x_640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
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
    mut v_msg_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
    mut v___y_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
    mut v___y_651_: *mut LeanObject,
    mut v___y_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_653_: *mut LeanObject = core::ptr::null_mut();
    v_res_653_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
        v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_,
    );
    lean_dec(v___y_651_);
    lean_dec_ref(v___y_650_);
    lean_dec(v___y_649_);
    lean_dec_ref(v___y_648_);
    return v_res_653_;
}
pub unsafe fn _init_l_Lean_Meta_Iterator_head___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Iterator_head___redArg___closed__0;
    v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
    return v___x_656_;
}
pub unsafe fn l_Lean_Meta_Iterator_head___redArg(
    mut v_L_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut v_unused_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_682_: u8 = 0;
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_686_: u8 = 0;
    let mut v_a_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_661_);
                lean_inc_ref(v_a_660_);
                lean_inc(v_a_659_);
                lean_inc_ref(v_a_658_);
                v___x_663_ = lean_apply_5(
                    v_L_657_,
                    v_a_658_,
                    v_a_659_,
                    v_a_660_,
                    v_a_661_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_663_) == 0 {
                    v_a_664_ = lean_ctor_get(v___x_663_, 0);
                    lean_inc(v_a_664_);
                    lean_dec_ref_known(v___x_663_, 1);
                    if lean_obj_tag(v_a_664_) == 0 {
                        v___x_665_ = lean_obj_once(
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
                        v_val_667_ = lean_ctor_get(v_a_664_, 0);
                        lean_inc(v_val_667_);
                        lean_dec_ref_known(v_a_664_, 1);
                        v_fst_668_ = lean_ctor_get(v_val_667_, 0);
                        lean_inc(v_fst_668_);
                        v_snd_669_ = lean_ctor_get(v_val_667_, 1);
                        lean_inc(v_snd_669_);
                        lean_dec(v_val_667_);
                        v___x_670_ =
                            l_Lean_Meta_SavedState_restore___redArg(v_snd_669_, v_a_659_, v_a_661_);
                        lean_dec(v_snd_669_);
                        if lean_obj_tag(v___x_670_) == 0 {
                            v_isSharedCheck_677_ = (!lean_is_exclusive(v___x_670_)) as u8;
                            if v_isSharedCheck_677_ == 0 {
                                v_unused_678_ = lean_ctor_get(v___x_670_, 0);
                                lean_dec(v_unused_678_);
                                v___x_672_ = v___x_670_;
                                v_isShared_673_ = v_isSharedCheck_677_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_670_);
                                v___x_672_ = lean_box(0);
                                v_isShared_673_ = v_isSharedCheck_677_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_668_);
                            v_a_679_ = lean_ctor_get(v___x_670_, 0);
                            v_isSharedCheck_686_ = (!lean_is_exclusive(v___x_670_)) as u8;
                            if v_isSharedCheck_686_ == 0 {
                                v___x_681_ = v___x_670_;
                                v_isShared_682_ = v_isSharedCheck_686_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_679_);
                                lean_dec(v___x_670_);
                                v___x_681_ = lean_box(0);
                                v_isShared_682_ = v_isSharedCheck_686_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_687_ = lean_ctor_get(v___x_663_, 0);
                    v_isSharedCheck_694_ = (!lean_is_exclusive(v___x_663_)) as u8;
                    if v_isSharedCheck_694_ == 0 {
                        v___x_689_ = v___x_663_;
                        v_isShared_690_ = v_isSharedCheck_694_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_687_);
                        lean_dec(v___x_663_);
                        v___x_689_ = lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_694_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_673_ == 0 {
                    lean_ctor_set(v___x_672_, 0, v_fst_668_);
                    v___x_675_ = v___x_672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_668_);
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
                    v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
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
                    v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
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
    mut v_L_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_701_: *mut LeanObject = core::ptr::null_mut();
    v_res_701_ =
        l_Lean_Meta_Iterator_head___redArg(v_L_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
    lean_dec(v_a_699_);
    lean_dec_ref(v_a_698_);
    lean_dec(v_a_697_);
    lean_dec_ref(v_a_696_);
    return v_res_701_;
}
pub unsafe fn l_Lean_Meta_Iterator_head(
    mut v_00_u03b1_702_: *mut LeanObject,
    mut v_L_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
    mut v_a_706_: *mut LeanObject,
    mut v_a_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ =
        l_Lean_Meta_Iterator_head___redArg(v_L_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
    return v___x_709_;
}
pub unsafe fn l_Lean_Meta_Iterator_head___boxed(
    mut v_00_u03b1_710_: *mut LeanObject,
    mut v_L_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
    mut v_a_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Meta_Iterator_head(
        v_00_u03b1_710_,
        v_L_711_,
        v_a_712_,
        v_a_713_,
        v_a_714_,
        v_a_715_,
    );
    lean_dec(v_a_715_);
    lean_dec_ref(v_a_714_);
    lean_dec(v_a_713_);
    lean_dec_ref(v_a_712_);
    return v_res_717_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(
    mut v_00_u03b1_718_: *mut LeanObject,
    mut v_msg_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
    mut v___y_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___redArg(
        v_msg_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_,
    );
    return v___x_725_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0___boxed(
    mut v_00_u03b1_726_: *mut LeanObject,
    mut v_msg_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_733_: *mut LeanObject = core::ptr::null_mut();
    v_res_733_ = l_Lean_throwError___at___00Lean_Meta_Iterator_head_spec__0(
        v_00_u03b1_726_,
        v_msg_727_,
        v___y_728_,
        v___y_729_,
        v___y_730_,
        v___y_731_,
    );
    lean_dec(v___y_731_);
    lean_dec_ref(v___y_730_);
    lean_dec(v___y_729_);
    lean_dec_ref(v___y_728_);
    return v_res_733_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___redArg(
    mut v_L_734_: *mut LeanObject,
    mut v_f_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_741_ = lean_alloc_closure(
        l___private_Lean_Meta_Iterator_0__Lean_Meta_Iterator_filterMapM___next___boxed
            as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___x_741_, 0, lean_box(0));
    lean_closure_set(v___x_741_, 1, lean_box(0));
    lean_closure_set(v___x_741_, 2, v_f_735_);
    lean_closure_set(v___x_741_, 3, v_L_734_);
    v___x_742_ =
        l_Lean_Meta_Iterator_head___redArg(v___x_741_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
    return v___x_742_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___redArg___boxed(
    mut v_L_743_: *mut LeanObject,
    mut v_f_744_: *mut LeanObject,
    mut v_a_745_: *mut LeanObject,
    mut v_a_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
    mut v_a_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_750_: *mut LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Lean_Meta_Iterator_firstM___redArg(
        v_L_743_, v_f_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_,
    );
    lean_dec(v_a_748_);
    lean_dec_ref(v_a_747_);
    lean_dec(v_a_746_);
    lean_dec_ref(v_a_745_);
    return v_res_750_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM(
    mut v_00_u03b1_751_: *mut LeanObject,
    mut v_00_u03b2_752_: *mut LeanObject,
    mut v_L_753_: *mut LeanObject,
    mut v_f_754_: *mut LeanObject,
    mut v_a_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Lean_Meta_Iterator_firstM___redArg(
        v_L_753_, v_f_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_,
    );
    return v___x_760_;
}
pub unsafe fn l_Lean_Meta_Iterator_firstM___boxed(
    mut v_00_u03b1_761_: *mut LeanObject,
    mut v_00_u03b2_762_: *mut LeanObject,
    mut v_L_763_: *mut LeanObject,
    mut v_f_764_: *mut LeanObject,
    mut v_a_765_: *mut LeanObject,
    mut v_a_766_: *mut LeanObject,
    mut v_a_767_: *mut LeanObject,
    mut v_a_768_: *mut LeanObject,
    mut v_a_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_770_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_768_);
    lean_dec_ref(v_a_767_);
    lean_dec(v_a_766_);
    lean_dec_ref(v_a_765_);
    return v_res_770_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Iterator(builtin);
}
