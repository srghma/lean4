// Lean compiler output
// Module: Init.Control.Option
// Imports: Init.Data.Option.Basic Init.Control.MonadAttach
use crate::r#gen::Init::Control::MonadAttach::{
    initialize_Init_Control_MonadAttach, runtime_initialize_Init_Control_MonadAttach,
};
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, l_Option_isSome___boxed,
    runtime_initialize_Init_Data_Option_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_instToBoolOption___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_isSome___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instToBoolOption___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instToBoolOption___closed__0_value) as *mut LeanObject;
pub static l_OptionT_instMonadFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_OptionT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_OptionT_instMonadFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_OptionT_instMonadFunctor___closed__0_value) as *mut LeanObject;
pub static l_OptionT_instMonadAttach___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_OptionT_instMonadAttach___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_OptionT_instMonadAttach___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_OptionT_instMonadAttach___redArg___closed__0_value) as *mut LeanObject;
pub static l_instMonadControlOptionTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlOptionTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlOptionTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_instMonadControlOptionTOfMonad___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlOptionTOfMonad___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlOptionTOfMonad___redArg___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_instToBoolOption(mut v_00_u03b1_429_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    v___x_430_ = l_instToBoolOption___closed__0;
    return v___x_430_;
}
pub unsafe fn l_OptionT_run___redArg(mut v_x_431_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_431_);
    return v_x_431_;
}
pub unsafe fn l_OptionT_run___redArg___boxed(mut v_x_432_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_433_: *mut LeanObject = core::ptr::null_mut();
    v_res_433_ = l_OptionT_run___redArg(v_x_432_);
    lean_dec(v_x_432_);
    return v_res_433_;
}
pub unsafe fn l_OptionT_run(
    mut v_m_434_: *mut LeanObject,
    mut v_00_u03b1_435_: *mut LeanObject,
    mut v_x_436_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_436_);
    return v_x_436_;
}
pub unsafe fn l_OptionT_run___boxed(
    mut v_m_437_: *mut LeanObject,
    mut v_00_u03b1_438_: *mut LeanObject,
    mut v_x_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_440_: *mut LeanObject = core::ptr::null_mut();
    v_res_440_ = l_OptionT_run(v_m_437_, v_00_u03b1_438_, v_x_439_);
    lean_dec(v_x_439_);
    return v_res_440_;
}
pub unsafe fn l_OptionT_mk___redArg(mut v_x_441_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_x_441_);
    return v_x_441_;
}
pub unsafe fn l_OptionT_mk___redArg___boxed(mut v_x_442_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_443_: *mut LeanObject = core::ptr::null_mut();
    v_res_443_ = l_OptionT_mk___redArg(v_x_442_);
    lean_dec(v_x_442_);
    return v_res_443_;
}
pub unsafe fn l_OptionT_mk(
    mut v_m_444_: *mut LeanObject,
    mut v_00_u03b1_445_: *mut LeanObject,
    mut v_x_446_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_446_);
    return v_x_446_;
}
pub unsafe fn l_OptionT_mk___boxed(
    mut v_m_447_: *mut LeanObject,
    mut v_00_u03b1_448_: *mut LeanObject,
    mut v_x_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_450_: *mut LeanObject = core::ptr::null_mut();
    v_res_450_ = l_OptionT_mk(v_m_447_, v_00_u03b1_448_, v_x_449_);
    lean_dec(v_x_449_);
    return v_res_450_;
}
pub unsafe fn l_OptionT_bind___redArg___lam__0(
    mut v_toPure_451_: *mut LeanObject,
    mut v_f_452_: *mut LeanObject,
    mut v_____do__lift_453_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_453_) == 0 {
        let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_452_);
        v___x_454_ = lean_box(0);
        v___x_455_ = lean_apply_2(v_toPure_451_, lean_box(0), v___x_454_);
        return v___x_455_;
    } else {
        let mut v_val_456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_451_);
        v_val_456_ = lean_ctor_get(v_____do__lift_453_, 0);
        lean_inc(v_val_456_);
        lean_dec_ref_known(v_____do__lift_453_, 1);
        v___x_457_ = lean_apply_1(v_f_452_, v_val_456_);
        return v___x_457_;
    }
}
pub unsafe fn l_OptionT_bind___redArg(
    mut v_inst_458_: *mut LeanObject,
    mut v_x_459_: *mut LeanObject,
    mut v_f_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_461_ = lean_ctor_get(v_inst_458_, 0);
    lean_inc_ref(v_toApplicative_461_);
    v_toBind_462_ = lean_ctor_get(v_inst_458_, 1);
    lean_inc(v_toBind_462_);
    lean_dec_ref(v_inst_458_);
    v_toPure_463_ = lean_ctor_get(v_toApplicative_461_, 1);
    lean_inc(v_toPure_463_);
    lean_dec_ref(v_toApplicative_461_);
    v___f_464_ = lean_alloc_closure(
        l_OptionT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_464_, 0, v_toPure_463_);
    lean_closure_set(v___f_464_, 1, v_f_460_);
    v___x_465_ = lean_apply_4(
        v_toBind_462_,
        lean_box(0),
        lean_box(0),
        v_x_459_,
        v___f_464_,
    );
    return v___x_465_;
}
pub unsafe fn l_OptionT_bind(
    mut v_m_466_: *mut LeanObject,
    mut v_inst_467_: *mut LeanObject,
    mut v_00_u03b1_468_: *mut LeanObject,
    mut v_00_u03b2_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
    mut v_f_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_472_ = lean_ctor_get(v_inst_467_, 0);
    lean_inc_ref(v_toApplicative_472_);
    v_toBind_473_ = lean_ctor_get(v_inst_467_, 1);
    lean_inc(v_toBind_473_);
    lean_dec_ref(v_inst_467_);
    v_toPure_474_ = lean_ctor_get(v_toApplicative_472_, 1);
    lean_inc(v_toPure_474_);
    lean_dec_ref(v_toApplicative_472_);
    v___f_475_ = lean_alloc_closure(
        l_OptionT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_475_, 0, v_toPure_474_);
    lean_closure_set(v___f_475_, 1, v_f_471_);
    v___x_476_ = lean_apply_4(
        v_toBind_473_,
        lean_box(0),
        lean_box(0),
        v_x_470_,
        v___f_475_,
    );
    return v___x_476_;
}
pub unsafe fn l_OptionT_pure___redArg(
    mut v_inst_477_: *mut LeanObject,
    mut v_a_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_479_ = lean_ctor_get(v_inst_477_, 0);
    lean_inc_ref(v_toApplicative_479_);
    lean_dec_ref(v_inst_477_);
    v_toPure_480_ = lean_ctor_get(v_toApplicative_479_, 1);
    lean_inc(v_toPure_480_);
    lean_dec_ref(v_toApplicative_479_);
    v___x_481_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_481_, 0, v_a_478_);
    v___x_482_ = lean_apply_2(v_toPure_480_, lean_box(0), v___x_481_);
    return v___x_482_;
}
pub unsafe fn l_OptionT_pure(
    mut v_m_483_: *mut LeanObject,
    mut v_inst_484_: *mut LeanObject,
    mut v_00_u03b1_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_487_ = lean_ctor_get(v_inst_484_, 0);
    lean_inc_ref(v_toApplicative_487_);
    lean_dec_ref(v_inst_484_);
    v_toPure_488_ = lean_ctor_get(v_toApplicative_487_, 1);
    lean_inc(v_toPure_488_);
    lean_dec_ref(v_toApplicative_487_);
    v___x_489_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_489_, 0, v_a_486_);
    v___x_490_ = lean_apply_2(v_toPure_488_, lean_box(0), v___x_489_);
    return v___x_490_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__0(
    mut v_toPure_491_: *mut LeanObject,
    mut v_f_492_: *mut LeanObject,
    mut v_____do__lift_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_493_) == 0 {
                    lean_dec(v_f_492_);
                    v___x_494_ = lean_box(0);
                    v___x_495_ = lean_apply_2(v_toPure_491_, lean_box(0), v___x_494_);
                    return v___x_495_;
                } else {
                    v_val_496_ = lean_ctor_get(v_____do__lift_493_, 0);
                    v_isSharedCheck_505_ = (!lean_is_exclusive(v_____do__lift_493_)) as u8;
                    if v_isSharedCheck_505_ == 0 {
                        v___x_498_ = v_____do__lift_493_;
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_496_);
                        lean_dec(v_____do__lift_493_);
                        v___x_498_ = lean_box(0);
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_500_ = lean_apply_1(v_f_492_, v_val_496_);
                if v_isShared_499_ == 0 {
                    lean_ctor_set(v___x_498_, 0, v___x_500_);
                    v___x_502_ = v___x_498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_500_);
                    v___x_502_ = v_reuseFailAlloc_504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_503_ = lean_apply_2(v_toPure_491_, lean_box(0), v___x_502_);
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__1(
    mut v_inst_506_: *mut LeanObject,
    mut v_00_u03b1_507_: *mut LeanObject,
    mut v_00_u03b2_508_: *mut LeanObject,
    mut v_f_509_: *mut LeanObject,
    mut v_x_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_511_ = lean_ctor_get(v_inst_506_, 0);
    lean_inc_ref(v_toApplicative_511_);
    v_toBind_512_ = lean_ctor_get(v_inst_506_, 1);
    lean_inc(v_toBind_512_);
    lean_dec_ref(v_inst_506_);
    v_toPure_513_ = lean_ctor_get(v_toApplicative_511_, 1);
    lean_inc(v_toPure_513_);
    lean_dec_ref(v_toApplicative_511_);
    v___f_514_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_514_, 0, v_toPure_513_);
    lean_closure_set(v___f_514_, 1, v_f_509_);
    v___x_515_ = lean_apply_4(
        v_toBind_512_,
        lean_box(0),
        lean_box(0),
        v_x_510_,
        v___f_514_,
    );
    return v___x_515_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__2(
    mut v_toPure_516_: *mut LeanObject,
    mut v___y_517_: *mut LeanObject,
    mut v_____do__lift_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut v_unused_529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_518_) == 0 {
                    lean_dec(v___y_517_);
                    v___x_519_ = lean_box(0);
                    v___x_520_ = lean_apply_2(v_toPure_516_, lean_box(0), v___x_519_);
                    return v___x_520_;
                } else {
                    v_isSharedCheck_528_ = (!lean_is_exclusive(v_____do__lift_518_)) as u8;
                    if v_isSharedCheck_528_ == 0 {
                        v_unused_529_ = lean_ctor_get(v_____do__lift_518_, 0);
                        lean_dec(v_unused_529_);
                        v___x_522_ = v_____do__lift_518_;
                        v_isShared_523_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_____do__lift_518_);
                        v___x_522_ = lean_box(0);
                        v_isShared_523_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_523_ == 0 {
                    lean_ctor_set(v___x_522_, 0, v___y_517_);
                    v___x_525_ = v___x_522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_527_, 0, v___y_517_);
                    v___x_525_ = v_reuseFailAlloc_527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_526_ = lean_apply_2(v_toPure_516_, lean_box(0), v___x_525_);
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__3(
    mut v_inst_530_: *mut LeanObject,
    mut v_00_u03b1_531_: *mut LeanObject,
    mut v_00_u03b2_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_535_ = lean_ctor_get(v_inst_530_, 0);
    lean_inc_ref(v_toApplicative_535_);
    v_toBind_536_ = lean_ctor_get(v_inst_530_, 1);
    lean_inc(v_toBind_536_);
    lean_dec_ref(v_inst_530_);
    v_toPure_537_ = lean_ctor_get(v_toApplicative_535_, 1);
    lean_inc(v_toPure_537_);
    lean_dec_ref(v_toApplicative_535_);
    v___f_538_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_538_, 0, v_toPure_537_);
    lean_closure_set(v___f_538_, 1, v___y_533_);
    v___x_539_ = lean_apply_4(
        v_toBind_536_,
        lean_box(0),
        lean_box(0),
        v___y_534_,
        v___f_538_,
    );
    return v___x_539_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__4(
    mut v_toPure_540_: *mut LeanObject,
    mut v_val_541_: *mut LeanObject,
    mut v_____do__lift_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_542_) == 0 {
                    lean_dec(v_val_541_);
                    v___x_543_ = lean_box(0);
                    v___x_544_ = lean_apply_2(v_toPure_540_, lean_box(0), v___x_543_);
                    return v___x_544_;
                } else {
                    v_val_545_ = lean_ctor_get(v_____do__lift_542_, 0);
                    v_isSharedCheck_554_ = (!lean_is_exclusive(v_____do__lift_542_)) as u8;
                    if v_isSharedCheck_554_ == 0 {
                        v___x_547_ = v_____do__lift_542_;
                        v_isShared_548_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_545_);
                        lean_dec(v_____do__lift_542_);
                        v___x_547_ = lean_box(0);
                        v_isShared_548_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_549_ = lean_apply_1(v_val_541_, v_val_545_);
                if v_isShared_548_ == 0 {
                    lean_ctor_set(v___x_547_, 0, v___x_549_);
                    v___x_551_ = v___x_547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
                    v___x_551_ = v_reuseFailAlloc_553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_552_ = lean_apply_2(v_toPure_540_, lean_box(0), v___x_551_);
                return v___x_552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__5(
    mut v_toPure_555_: *mut LeanObject,
    mut v_x_556_: *mut LeanObject,
    mut v_toBind_557_: *mut LeanObject,
    mut v_____do__lift_558_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_558_) == 0 {
        let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_557_);
        lean_dec(v_x_556_);
        v___x_559_ = lean_box(0);
        v___x_560_ = lean_apply_2(v_toPure_555_, lean_box(0), v___x_559_);
        return v___x_560_;
    } else {
        let mut v_val_561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
        v_val_561_ = lean_ctor_get(v_____do__lift_558_, 0);
        lean_inc(v_val_561_);
        lean_dec_ref_known(v_____do__lift_558_, 1);
        v___f_562_ = lean_alloc_closure(
            l_OptionT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_562_, 0, v_toPure_555_);
        lean_closure_set(v___f_562_, 1, v_val_561_);
        v___x_563_ = lean_box(0);
        v___x_564_ = lean_apply_1(v_x_556_, v___x_563_);
        v___x_565_ = lean_apply_4(
            v_toBind_557_,
            lean_box(0),
            lean_box(0),
            v___x_564_,
            v___f_562_,
        );
        return v___x_565_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__6(
    mut v_inst_566_: *mut LeanObject,
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_00_u03b2_568_: *mut LeanObject,
    mut v_f_569_: *mut LeanObject,
    mut v_x_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_571_ = lean_ctor_get(v_inst_566_, 0);
    lean_inc_ref(v_toApplicative_571_);
    v_toBind_572_ = lean_ctor_get(v_inst_566_, 1);
    lean_inc_n(v_toBind_572_, 2);
    lean_dec_ref(v_inst_566_);
    v_toPure_573_ = lean_ctor_get(v_toApplicative_571_, 1);
    lean_inc(v_toPure_573_);
    lean_dec_ref(v_toApplicative_571_);
    v___f_574_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_574_, 0, v_toPure_573_);
    lean_closure_set(v___f_574_, 1, v_x_570_);
    lean_closure_set(v___f_574_, 2, v_toBind_572_);
    v___x_575_ = lean_apply_4(
        v_toBind_572_,
        lean_box(0),
        lean_box(0),
        v_f_569_,
        v___f_574_,
    );
    return v___x_575_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__7(
    mut v_toPure_576_: *mut LeanObject,
    mut v_____do__lift_577_: *mut LeanObject,
    mut v_____do__lift_578_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_578_) == 0 {
        let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_____do__lift_577_);
        v___x_579_ = lean_box(0);
        v___x_580_ = lean_apply_2(v_toPure_576_, lean_box(0), v___x_579_);
        return v___x_580_;
    } else {
        let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
        v___x_581_ = lean_apply_2(v_toPure_576_, lean_box(0), v_____do__lift_577_);
        return v___x_581_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__7___boxed(
    mut v_toPure_582_: *mut LeanObject,
    mut v_____do__lift_583_: *mut LeanObject,
    mut v_____do__lift_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_585_: *mut LeanObject = core::ptr::null_mut();
    v_res_585_ = l_OptionT_instMonad___redArg___lam__7(
        v_toPure_582_,
        v_____do__lift_583_,
        v_____do__lift_584_,
    );
    lean_dec(v_____do__lift_584_);
    return v_res_585_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__8(
    mut v_toPure_586_: *mut LeanObject,
    mut v_y_587_: *mut LeanObject,
    mut v_toBind_588_: *mut LeanObject,
    mut v_____do__lift_589_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_589_) == 0 {
        let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_588_);
        lean_dec(v_y_587_);
        v___x_590_ = lean_apply_2(v_toPure_586_, lean_box(0), v_____do__lift_589_);
        return v___x_590_;
    } else {
        let mut v___f_591_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
        v___f_591_ = lean_alloc_closure(
            l_OptionT_instMonad___redArg___lam__7___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_591_, 0, v_toPure_586_);
        lean_closure_set(v___f_591_, 1, v_____do__lift_589_);
        v___x_592_ = lean_box(0);
        v___x_593_ = lean_apply_1(v_y_587_, v___x_592_);
        v___x_594_ = lean_apply_4(
            v_toBind_588_,
            lean_box(0),
            lean_box(0),
            v___x_593_,
            v___f_591_,
        );
        return v___x_594_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__9(
    mut v_inst_595_: *mut LeanObject,
    mut v_00_u03b1_596_: *mut LeanObject,
    mut v_00_u03b2_597_: *mut LeanObject,
    mut v_x_598_: *mut LeanObject,
    mut v_y_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_600_ = lean_ctor_get(v_inst_595_, 0);
    lean_inc_ref(v_toApplicative_600_);
    v_toBind_601_ = lean_ctor_get(v_inst_595_, 1);
    lean_inc_n(v_toBind_601_, 2);
    lean_dec_ref(v_inst_595_);
    v_toPure_602_ = lean_ctor_get(v_toApplicative_600_, 1);
    lean_inc(v_toPure_602_);
    lean_dec_ref(v_toApplicative_600_);
    v___f_603_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_603_, 0, v_toPure_602_);
    lean_closure_set(v___f_603_, 1, v_y_599_);
    lean_closure_set(v___f_603_, 2, v_toBind_601_);
    v___x_604_ = lean_apply_4(
        v_toBind_601_,
        lean_box(0),
        lean_box(0),
        v_x_598_,
        v___f_603_,
    );
    return v___x_604_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__10(
    mut v_toPure_605_: *mut LeanObject,
    mut v_y_606_: *mut LeanObject,
    mut v_____do__lift_607_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_607_) == 0 {
        let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_y_606_);
        v___x_608_ = lean_box(0);
        v___x_609_ = lean_apply_2(v_toPure_605_, lean_box(0), v___x_608_);
        return v___x_609_;
    } else {
        let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_605_);
        v___x_610_ = lean_box(0);
        v___x_611_ = lean_apply_1(v_y_606_, v___x_610_);
        return v___x_611_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__10___boxed(
    mut v_toPure_612_: *mut LeanObject,
    mut v_y_613_: *mut LeanObject,
    mut v_____do__lift_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_615_: *mut LeanObject = core::ptr::null_mut();
    v_res_615_ =
        l_OptionT_instMonad___redArg___lam__10(v_toPure_612_, v_y_613_, v_____do__lift_614_);
    lean_dec(v_____do__lift_614_);
    return v_res_615_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__11(
    mut v_inst_616_: *mut LeanObject,
    mut v_00_u03b1_617_: *mut LeanObject,
    mut v_00_u03b2_618_: *mut LeanObject,
    mut v_x_619_: *mut LeanObject,
    mut v_y_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_621_ = lean_ctor_get(v_inst_616_, 0);
    lean_inc_ref(v_toApplicative_621_);
    v_toBind_622_ = lean_ctor_get(v_inst_616_, 1);
    lean_inc(v_toBind_622_);
    lean_dec_ref(v_inst_616_);
    v_toPure_623_ = lean_ctor_get(v_toApplicative_621_, 1);
    lean_inc(v_toPure_623_);
    lean_dec_ref(v_toApplicative_621_);
    v___f_624_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__10___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_624_, 0, v_toPure_623_);
    lean_closure_set(v___f_624_, 1, v_y_620_);
    v___x_625_ = lean_apply_4(
        v_toBind_622_,
        lean_box(0),
        lean_box(0),
        v_x_619_,
        v___f_624_,
    );
    return v___x_625_;
}
pub unsafe fn l_OptionT_instMonad___redArg(mut v_inst_626_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_626_, 6);
    v___f_627_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_627_, 0, v_inst_626_);
    v___f_628_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_628_, 0, v_inst_626_);
    v___f_629_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_629_, 0, v_inst_626_);
    v___f_630_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_630_, 0, v_inst_626_);
    v___f_631_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_631_, 0, v_inst_626_);
    v___x_632_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_632_, 0, v___f_627_);
    lean_ctor_set(v___x_632_, 1, v___f_628_);
    v___x_633_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_633_, 0, lean_box(0));
    lean_closure_set(v___x_633_, 1, v_inst_626_);
    v___x_634_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_634_, 0, v___x_632_);
    lean_ctor_set(v___x_634_, 1, v___x_633_);
    lean_ctor_set(v___x_634_, 2, v___f_629_);
    lean_ctor_set(v___x_634_, 3, v___f_630_);
    lean_ctor_set(v___x_634_, 4, v___f_631_);
    v___x_635_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___x_635_, 0, lean_box(0));
    lean_closure_set(v___x_635_, 1, v_inst_626_);
    v___x_636_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_636_, 0, v___x_634_);
    lean_ctor_set(v___x_636_, 1, v___x_635_);
    return v___x_636_;
}
pub unsafe fn l_OptionT_instMonad(
    mut v_m_637_: *mut LeanObject,
    mut v_inst_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_638_, 6);
    v___f_639_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_639_, 0, v_inst_638_);
    v___f_640_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_640_, 0, v_inst_638_);
    v___f_641_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_641_, 0, v_inst_638_);
    v___f_642_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_642_, 0, v_inst_638_);
    v___f_643_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_643_, 0, v_inst_638_);
    v___x_644_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_644_, 0, v___f_639_);
    lean_ctor_set(v___x_644_, 1, v___f_640_);
    v___x_645_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_645_, 0, lean_box(0));
    lean_closure_set(v___x_645_, 1, v_inst_638_);
    v___x_646_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_646_, 0, v___x_644_);
    lean_ctor_set(v___x_646_, 1, v___x_645_);
    lean_ctor_set(v___x_646_, 2, v___f_641_);
    lean_ctor_set(v___x_646_, 3, v___f_642_);
    lean_ctor_set(v___x_646_, 4, v___f_643_);
    v___x_647_ = lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
    lean_closure_set(v___x_647_, 0, lean_box(0));
    lean_closure_set(v___x_647_, 1, v_inst_638_);
    v___x_648_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_648_, 0, v___x_646_);
    lean_ctor_set(v___x_648_, 1, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l_OptionT_instInhabitedOfPure___redArg(
    mut v_inst_649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    v___x_650_ = lean_box(0);
    v___x_651_ = lean_apply_2(v_inst_649_, lean_box(0), v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_OptionT_instInhabitedOfPure(
    mut v_00_u03b1_652_: *mut LeanObject,
    mut v_m_653_: *mut LeanObject,
    mut v_inst_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = l_OptionT_instInhabitedOfPure___redArg(v_inst_654_);
    return v___x_655_;
}
pub unsafe fn l_OptionT_orElse___redArg___lam__0(
    mut v_y_656_: *mut LeanObject,
    mut v_toPure_657_: *mut LeanObject,
    mut v_____do__lift_658_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_658_) == 0 {
        let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_657_);
        v___x_659_ = lean_box(0);
        v___x_660_ = lean_apply_1(v_y_656_, v___x_659_);
        return v___x_660_;
    } else {
        let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_y_656_);
        v___x_661_ = lean_apply_2(v_toPure_657_, lean_box(0), v_____do__lift_658_);
        return v___x_661_;
    }
}
pub unsafe fn l_OptionT_orElse___redArg(
    mut v_inst_662_: *mut LeanObject,
    mut v_x_663_: *mut LeanObject,
    mut v_y_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_665_ = lean_ctor_get(v_inst_662_, 0);
    lean_inc_ref(v_toApplicative_665_);
    v_toBind_666_ = lean_ctor_get(v_inst_662_, 1);
    lean_inc(v_toBind_666_);
    lean_dec_ref(v_inst_662_);
    v_toPure_667_ = lean_ctor_get(v_toApplicative_665_, 1);
    lean_inc(v_toPure_667_);
    lean_dec_ref(v_toApplicative_665_);
    v___f_668_ = lean_alloc_closure(
        l_OptionT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_668_, 0, v_y_664_);
    lean_closure_set(v___f_668_, 1, v_toPure_667_);
    v___x_669_ = lean_apply_4(
        v_toBind_666_,
        lean_box(0),
        lean_box(0),
        v_x_663_,
        v___f_668_,
    );
    return v___x_669_;
}
pub unsafe fn l_OptionT_orElse(
    mut v_m_670_: *mut LeanObject,
    mut v_inst_671_: *mut LeanObject,
    mut v_00_u03b1_672_: *mut LeanObject,
    mut v_x_673_: *mut LeanObject,
    mut v_y_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_675_ = lean_ctor_get(v_inst_671_, 0);
    lean_inc_ref(v_toApplicative_675_);
    v_toBind_676_ = lean_ctor_get(v_inst_671_, 1);
    lean_inc(v_toBind_676_);
    lean_dec_ref(v_inst_671_);
    v_toPure_677_ = lean_ctor_get(v_toApplicative_675_, 1);
    lean_inc(v_toPure_677_);
    lean_dec_ref(v_toApplicative_675_);
    v___f_678_ = lean_alloc_closure(
        l_OptionT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_678_, 0, v_y_674_);
    lean_closure_set(v___f_678_, 1, v_toPure_677_);
    v___x_679_ = lean_apply_4(
        v_toBind_676_,
        lean_box(0),
        lean_box(0),
        v_x_673_,
        v___f_678_,
    );
    return v___x_679_;
}
pub unsafe fn l_OptionT_fail___redArg(mut v_inst_680_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toApplicative_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_681_ = lean_ctor_get(v_inst_680_, 0);
    lean_inc_ref(v_toApplicative_681_);
    lean_dec_ref(v_inst_680_);
    v_toPure_682_ = lean_ctor_get(v_toApplicative_681_, 1);
    lean_inc(v_toPure_682_);
    lean_dec_ref(v_toApplicative_681_);
    v___x_683_ = lean_box(0);
    v___x_684_ = lean_apply_2(v_toPure_682_, lean_box(0), v___x_683_);
    return v___x_684_;
}
pub unsafe fn l_OptionT_fail(
    mut v_m_685_: *mut LeanObject,
    mut v_inst_686_: *mut LeanObject,
    mut v_00_u03b1_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_688_ = lean_ctor_get(v_inst_686_, 0);
    lean_inc_ref(v_toApplicative_688_);
    lean_dec_ref(v_inst_686_);
    v_toPure_689_ = lean_ctor_get(v_toApplicative_688_, 1);
    lean_inc(v_toPure_689_);
    lean_dec_ref(v_toApplicative_688_);
    v___x_690_ = lean_box(0);
    v___x_691_ = lean_apply_2(v_toPure_689_, lean_box(0), v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_OptionT_instAlternative___redArg(
    mut v_inst_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_692_, 7);
    v___f_693_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_693_, 0, v_inst_692_);
    v___f_694_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_694_, 0, v_inst_692_);
    v___f_695_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_695_, 0, v_inst_692_);
    v___f_696_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_696_, 0, v_inst_692_);
    v___f_697_ = lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_697_, 0, v_inst_692_);
    v___x_698_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_698_, 0, v___f_693_);
    lean_ctor_set(v___x_698_, 1, v___f_694_);
    v___x_699_ = lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_699_, 0, lean_box(0));
    lean_closure_set(v___x_699_, 1, v_inst_692_);
    v___x_700_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_700_, 0, v___x_698_);
    lean_ctor_set(v___x_700_, 1, v___x_699_);
    lean_ctor_set(v___x_700_, 2, v___f_695_);
    lean_ctor_set(v___x_700_, 3, v___f_696_);
    lean_ctor_set(v___x_700_, 4, v___f_697_);
    v___x_701_ = lean_alloc_closure(l_OptionT_fail as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_701_, 0, lean_box(0));
    lean_closure_set(v___x_701_, 1, v_inst_692_);
    v___x_702_ = lean_alloc_closure(l_OptionT_orElse as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___x_702_, 0, lean_box(0));
    lean_closure_set(v___x_702_, 1, v_inst_692_);
    v___x_703_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_703_, 0, v___x_700_);
    lean_ctor_set(v___x_703_, 1, v___x_701_);
    lean_ctor_set(v___x_703_, 2, v___x_702_);
    return v___x_703_;
}
pub unsafe fn l_OptionT_instAlternative(
    mut v_m_704_: *mut LeanObject,
    mut v_inst_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = l_OptionT_instAlternative___redArg(v_inst_705_);
    return v___x_706_;
}
pub unsafe fn l_OptionT_lift___redArg___lam__0(
    mut v_toPure_707_: *mut LeanObject,
    mut v_____do__lift_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    v___x_709_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_709_, 0, v_____do__lift_708_);
    v___x_710_ = lean_apply_2(v_toPure_707_, lean_box(0), v___x_709_);
    return v___x_710_;
}
pub unsafe fn l_OptionT_lift___redArg(
    mut v_inst_711_: *mut LeanObject,
    mut v_x_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_713_ = lean_ctor_get(v_inst_711_, 0);
    lean_inc_ref(v_toApplicative_713_);
    v_toBind_714_ = lean_ctor_get(v_inst_711_, 1);
    lean_inc(v_toBind_714_);
    lean_dec_ref(v_inst_711_);
    v_toPure_715_ = lean_ctor_get(v_toApplicative_713_, 1);
    lean_inc(v_toPure_715_);
    lean_dec_ref(v_toApplicative_713_);
    v___f_716_ = lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_716_, 0, v_toPure_715_);
    v___x_717_ = lean_apply_4(
        v_toBind_714_,
        lean_box(0),
        lean_box(0),
        v_x_712_,
        v___f_716_,
    );
    return v___x_717_;
}
pub unsafe fn l_OptionT_lift(
    mut v_m_718_: *mut LeanObject,
    mut v_inst_719_: *mut LeanObject,
    mut v_00_u03b1_720_: *mut LeanObject,
    mut v_x_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_722_ = lean_ctor_get(v_inst_719_, 0);
    lean_inc_ref(v_toApplicative_722_);
    v_toBind_723_ = lean_ctor_get(v_inst_719_, 1);
    lean_inc(v_toBind_723_);
    lean_dec_ref(v_inst_719_);
    v_toPure_724_ = lean_ctor_get(v_toApplicative_722_, 1);
    lean_inc(v_toPure_724_);
    lean_dec_ref(v_toApplicative_722_);
    v___f_725_ = lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_725_, 0, v_toPure_724_);
    v___x_726_ = lean_apply_4(
        v_toBind_723_,
        lean_box(0),
        lean_box(0),
        v_x_721_,
        v___f_725_,
    );
    return v___x_726_;
}
pub unsafe fn l_OptionT_instMonadLift___redArg(
    mut v_inst_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_728_ = lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_728_, 0, lean_box(0));
    lean_closure_set(v___x_728_, 1, v_inst_727_);
    return v___x_728_;
}
pub unsafe fn l_OptionT_instMonadLift(
    mut v_m_729_: *mut LeanObject,
    mut v_inst_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___x_731_, 0, lean_box(0));
    lean_closure_set(v___x_731_, 1, v_inst_730_);
    return v___x_731_;
}
pub unsafe fn l_OptionT_instMonadFunctor___lam__0(
    mut v_00_u03b1_732_: *mut LeanObject,
    mut v_f_733_: *mut LeanObject,
    mut v_x_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ = lean_apply_2(v_f_733_, lean_box(0), v_x_734_);
    return v___x_735_;
}
pub unsafe fn l_OptionT_instMonadFunctor(mut v_m_737_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_738_: *mut LeanObject = core::ptr::null_mut();
    v___f_738_ = l_OptionT_instMonadFunctor___closed__0;
    return v___f_738_;
}
pub unsafe fn l_OptionT_tryCatch___redArg___lam__0(
    mut v_handle_739_: *mut LeanObject,
    mut v_toPure_740_: *mut LeanObject,
    mut v_____x_741_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_741_) == 0 {
        let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_740_);
        v___x_742_ = lean_box(0);
        v___x_743_ = lean_apply_1(v_handle_739_, v___x_742_);
        return v___x_743_;
    } else {
        let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_handle_739_);
        v___x_744_ = lean_apply_2(v_toPure_740_, lean_box(0), v_____x_741_);
        return v___x_744_;
    }
}
pub unsafe fn l_OptionT_tryCatch___redArg(
    mut v_inst_745_: *mut LeanObject,
    mut v_x_746_: *mut LeanObject,
    mut v_handle_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_748_ = lean_ctor_get(v_inst_745_, 0);
    lean_inc_ref(v_toApplicative_748_);
    v_toBind_749_ = lean_ctor_get(v_inst_745_, 1);
    lean_inc(v_toBind_749_);
    lean_dec_ref(v_inst_745_);
    v_toPure_750_ = lean_ctor_get(v_toApplicative_748_, 1);
    lean_inc(v_toPure_750_);
    lean_dec_ref(v_toApplicative_748_);
    v___f_751_ = lean_alloc_closure(
        l_OptionT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_751_, 0, v_handle_747_);
    lean_closure_set(v___f_751_, 1, v_toPure_750_);
    v___x_752_ = lean_apply_4(
        v_toBind_749_,
        lean_box(0),
        lean_box(0),
        v_x_746_,
        v___f_751_,
    );
    return v___x_752_;
}
pub unsafe fn l_OptionT_tryCatch(
    mut v_m_753_: *mut LeanObject,
    mut v_inst_754_: *mut LeanObject,
    mut v_00_u03b1_755_: *mut LeanObject,
    mut v_x_756_: *mut LeanObject,
    mut v_handle_757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_758_ = lean_ctor_get(v_inst_754_, 0);
    lean_inc_ref(v_toApplicative_758_);
    v_toBind_759_ = lean_ctor_get(v_inst_754_, 1);
    lean_inc(v_toBind_759_);
    lean_dec_ref(v_inst_754_);
    v_toPure_760_ = lean_ctor_get(v_toApplicative_758_, 1);
    lean_inc(v_toPure_760_);
    lean_dec_ref(v_toApplicative_758_);
    v___f_761_ = lean_alloc_closure(
        l_OptionT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_761_, 0, v_handle_757_);
    lean_closure_set(v___f_761_, 1, v_toPure_760_);
    v___x_762_ = lean_apply_4(
        v_toBind_759_,
        lean_box(0),
        lean_box(0),
        v_x_756_,
        v___f_761_,
    );
    return v___x_762_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(
    mut v_inst_763_: *mut LeanObject,
    mut v_00_u03b1_764_: *mut LeanObject,
    mut v_x_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_766_ = lean_ctor_get(v_inst_763_, 0);
    lean_inc_ref(v_toApplicative_766_);
    lean_dec_ref(v_inst_763_);
    v_toPure_767_ = lean_ctor_get(v_toApplicative_766_, 1);
    lean_inc(v_toPure_767_);
    lean_dec_ref(v_toApplicative_766_);
    v___x_768_ = lean_box(0);
    v___x_769_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_768_);
    return v___x_769_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit___redArg(
    mut v_inst_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_770_);
    v___f_771_ = lean_alloc_closure(
        l_OptionT_instMonadExceptOfPUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_771_, 0, v_inst_770_);
    v___x_772_ = lean_alloc_closure(l_OptionT_tryCatch as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___x_772_, 0, lean_box(0));
    lean_closure_set(v___x_772_, 1, v_inst_770_);
    v___x_773_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_773_, 0, v___f_771_);
    lean_ctor_set(v___x_773_, 1, v___x_772_);
    return v___x_773_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit(
    mut v_m_774_: *mut LeanObject,
    mut v_inst_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l_OptionT_instMonadExceptOfPUnit___redArg(v_inst_775_);
    return v___x_776_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg___lam__0(
    mut v_inst_777_: *mut LeanObject,
    mut v_00_u03b1_778_: *mut LeanObject,
    mut v_e_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v_throw_780_ = lean_ctor_get(v_inst_777_, 0);
    lean_inc(v_throw_780_);
    lean_dec_ref(v_inst_777_);
    v___x_781_ = lean_apply_2(v_throw_780_, lean_box(0), v_e_779_);
    return v___x_781_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg___lam__1(
    mut v_inst_782_: *mut LeanObject,
    mut v_00_u03b1_783_: *mut LeanObject,
    mut v_x_784_: *mut LeanObject,
    mut v_handle_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tryCatch_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    v_tryCatch_786_ = lean_ctor_get(v_inst_782_, 1);
    lean_inc(v_tryCatch_786_);
    lean_dec_ref(v_inst_782_);
    v___x_787_ = lean_apply_3(v_tryCatch_786_, lean_box(0), v_x_784_, v_handle_785_);
    return v___x_787_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg(
    mut v_inst_788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_788_);
    v___f_789_ = lean_alloc_closure(
        l_OptionT_instMonadExceptOf___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_789_, 0, v_inst_788_);
    v___f_790_ = lean_alloc_closure(
        l_OptionT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_790_, 0, v_inst_788_);
    v___x_791_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_791_, 0, v___f_789_);
    lean_ctor_set(v___x_791_, 1, v___f_790_);
    return v___x_791_;
}
pub unsafe fn l_OptionT_instMonadExceptOf(
    mut v_m_792_: *mut LeanObject,
    mut v_00_u03b5_793_: *mut LeanObject,
    mut v_inst_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    v___x_795_ = l_OptionT_instMonadExceptOf___redArg(v_inst_794_);
    return v___x_795_;
}
pub unsafe fn l_OptionT_instMonadAttach___redArg___lam__0(
    mut v_x_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_796_) == 0 {
                    v___x_797_ = lean_box(0);
                    return v___x_797_;
                } else {
                    v_val_798_ = lean_ctor_get(v_x_796_, 0);
                    v_isSharedCheck_805_ = (!lean_is_exclusive(v_x_796_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v_x_796_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_798_);
                        lean_dec(v_x_796_);
                        v___x_800_ = lean_box(0);
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_801_ == 0 {
                    v___x_803_ = v___x_800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_798_);
                    v___x_803_ = v_reuseFailAlloc_804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonadAttach___redArg___lam__1(
    mut v_toFunctor_806_: *mut LeanObject,
    mut v_inst_807_: *mut LeanObject,
    mut v___f_808_: *mut LeanObject,
    mut v_00_u03b1_809_: *mut LeanObject,
    mut v_x_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    v_map_811_ = lean_ctor_get(v_toFunctor_806_, 0);
    lean_inc(v_map_811_);
    lean_dec_ref(v_toFunctor_806_);
    v___x_812_ = lean_apply_2(v_inst_807_, lean_box(0), v_x_810_);
    v___x_813_ = lean_apply_4(v_map_811_, lean_box(0), lean_box(0), v___f_808_, v___x_812_);
    return v___x_813_;
}
pub unsafe fn l_OptionT_instMonadAttach___redArg(
    mut v_inst_815_: *mut LeanObject,
    mut v_inst_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_820_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_817_ = lean_ctor_get(v_inst_815_, 0);
    lean_inc_ref(v_toApplicative_817_);
    lean_dec_ref(v_inst_815_);
    v_toFunctor_818_ = lean_ctor_get(v_toApplicative_817_, 0);
    lean_inc_ref(v_toFunctor_818_);
    lean_dec_ref(v_toApplicative_817_);
    v___f_819_ = l_OptionT_instMonadAttach___redArg___closed__0;
    v___f_820_ = lean_alloc_closure(
        l_OptionT_instMonadAttach___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_820_, 0, v_toFunctor_818_);
    lean_closure_set(v___f_820_, 1, v_inst_816_);
    lean_closure_set(v___f_820_, 2, v___f_819_);
    return v___f_820_;
}
pub unsafe fn l_OptionT_instMonadAttach(
    mut v_m_821_: *mut LeanObject,
    mut v_inst_822_: *mut LeanObject,
    mut v_inst_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = l_OptionT_instMonadAttach___redArg(v_inst_822_, v_inst_823_);
    return v___x_824_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__0(
    mut v_00_u03b2_825_: *mut LeanObject,
    mut v_x_826_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_826_);
    return v_x_826_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(
    mut v_00_u03b2_827_: *mut LeanObject,
    mut v_x_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_829_: *mut LeanObject = core::ptr::null_mut();
    v_res_829_ = l_instMonadControlOptionTOfMonad___redArg___lam__0(v_00_u03b2_827_, v_x_828_);
    lean_dec(v_x_828_);
    return v_res_829_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__2(
    mut v_inst_830_: *mut LeanObject,
    mut v___f_831_: *mut LeanObject,
    mut v_00_u03b1_832_: *mut LeanObject,
    mut v_f_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_834_ = lean_ctor_get(v_inst_830_, 0);
    lean_inc_ref(v_toApplicative_834_);
    v_toBind_835_ = lean_ctor_get(v_inst_830_, 1);
    lean_inc(v_toBind_835_);
    lean_dec_ref(v_inst_830_);
    v_toPure_836_ = lean_ctor_get(v_toApplicative_834_, 1);
    lean_inc(v_toPure_836_);
    lean_dec_ref(v_toApplicative_834_);
    v___x_837_ = lean_apply_1(v_f_833_, v___f_831_);
    v___f_838_ = lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_838_, 0, v_toPure_836_);
    v___x_839_ = lean_apply_4(
        v_toBind_835_,
        lean_box(0),
        lean_box(0),
        v___x_837_,
        v___f_838_,
    );
    return v___x_839_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__1(
    mut v_00_u03b1_840_: *mut LeanObject,
    mut v_x_841_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_841_);
    return v_x_841_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(
    mut v_00_u03b1_842_: *mut LeanObject,
    mut v_x_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_844_: *mut LeanObject = core::ptr::null_mut();
    v_res_844_ = l_instMonadControlOptionTOfMonad___redArg___lam__1(v_00_u03b1_842_, v_x_843_);
    lean_dec(v_x_843_);
    return v_res_844_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg(
    mut v_inst_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    v___f_848_ = l_instMonadControlOptionTOfMonad___redArg___closed__0;
    v___f_849_ = lean_alloc_closure(
        l_instMonadControlOptionTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_849_, 0, v_inst_847_);
    lean_closure_set(v___f_849_, 1, v___f_848_);
    v___f_850_ = l_instMonadControlOptionTOfMonad___redArg___closed__1;
    v___x_851_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_851_, 0, v___f_849_);
    lean_ctor_set(v___x_851_, 1, v___f_850_);
    return v___x_851_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad(
    mut v_m_852_: *mut LeanObject,
    mut v_inst_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = l_instMonadControlOptionTOfMonad___redArg(v_inst_853_);
    return v___x_854_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Option(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_MonadAttach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Option(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Option(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_MonadAttach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Option(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Option(builtin);
}
