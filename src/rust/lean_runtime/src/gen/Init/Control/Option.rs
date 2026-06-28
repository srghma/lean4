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
pub static l_instToBoolOption___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Option_isSome___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instToBoolOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instToBoolOption___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_OptionT_instMonadFunctor___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_OptionT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_OptionT_instMonadFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_OptionT_instMonadFunctor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_OptionT_instMonadAttach___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_OptionT_instMonadAttach___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_OptionT_instMonadAttach___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_OptionT_instMonadAttach___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlOptionTOfMonad___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlOptionTOfMonad___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlOptionTOfMonad___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadControlOptionTOfMonad___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlOptionTOfMonad___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlOptionTOfMonad___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_instToBoolOption(
    mut v_00_u03b1_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ = l_instToBoolOption___closed__0;
    return v___x_430_;
}
pub unsafe fn l_OptionT_run___redArg(
    mut v_x_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_431_);
    return v_x_431_;
}
pub unsafe fn l_OptionT_run___redArg___boxed(
    mut v_x_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_OptionT_run___redArg(v_x_432_);
    crate::leanh::lean_dec(v_x_432_);
    return v_res_433_;
}
pub unsafe fn l_OptionT_run(
    mut v_m_434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_436_);
    return v_x_436_;
}
pub unsafe fn l_OptionT_run___boxed(
    mut v_m_437_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_438_: *mut crate::leanh::LeanObject,
    mut v_x_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_440_ = l_OptionT_run(v_m_437_, v_00_u03b1_438_, v_x_439_);
    crate::leanh::lean_dec(v_x_439_);
    return v_res_440_;
}
pub unsafe fn l_OptionT_mk___redArg(
    mut v_x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_441_);
    return v_x_441_;
}
pub unsafe fn l_OptionT_mk___redArg___boxed(
    mut v_x_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_OptionT_mk___redArg(v_x_442_);
    crate::leanh::lean_dec(v_x_442_);
    return v_res_443_;
}
pub unsafe fn l_OptionT_mk(
    mut v_m_444_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_445_: *mut crate::leanh::LeanObject,
    mut v_x_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_446_);
    return v_x_446_;
}
pub unsafe fn l_OptionT_mk___boxed(
    mut v_m_447_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_448_: *mut crate::leanh::LeanObject,
    mut v_x_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_OptionT_mk(v_m_447_, v_00_u03b1_448_, v_x_449_);
    crate::leanh::lean_dec(v_x_449_);
    return v_res_450_;
}
pub unsafe fn l_OptionT_bind___redArg___lam__0(
    mut v_toPure_451_: *mut crate::leanh::LeanObject,
    mut v_f_452_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_453_) == 0 {
        let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_452_);
        v___x_454_ = crate::leanh::lean_box(0);
        v___x_455_ =
            crate::leanh::lean_apply_2(v_toPure_451_, crate::leanh::lean_box(0), v___x_454_);
        return v___x_455_;
    } else {
        let mut v_val_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_451_);
        v_val_456_ = crate::leanh::lean_ctor_get(v_____do__lift_453_, 0);
        crate::leanh::lean_inc(v_val_456_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_453_, 1);
        v___x_457_ = crate::leanh::lean_apply_1(v_f_452_, v_val_456_);
        return v___x_457_;
    }
}
pub unsafe fn l_OptionT_bind___redArg(
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_x_459_: *mut crate::leanh::LeanObject,
    mut v_f_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_461_ = crate::leanh::lean_ctor_get(v_inst_458_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_461_);
    v_toBind_462_ = crate::leanh::lean_ctor_get(v_inst_458_, 1);
    crate::leanh::lean_inc(v_toBind_462_);
    crate::leanh::lean_dec_ref(v_inst_458_);
    v_toPure_463_ = crate::leanh::lean_ctor_get(v_toApplicative_461_, 1);
    crate::leanh::lean_inc(v_toPure_463_);
    crate::leanh::lean_dec_ref(v_toApplicative_461_);
    v___f_464_ = crate::leanh::lean_alloc_closure(
        l_OptionT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_464_, 0, v_toPure_463_);
    crate::leanh::lean_closure_set(v___f_464_, 1, v_f_460_);
    v___x_465_ = crate::leanh::lean_apply_4(
        v_toBind_462_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_459_,
        v___f_464_,
    );
    return v___x_465_;
}
pub unsafe fn l_OptionT_bind(
    mut v_m_466_: *mut crate::leanh::LeanObject,
    mut v_inst_467_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_469_: *mut crate::leanh::LeanObject,
    mut v_x_470_: *mut crate::leanh::LeanObject,
    mut v_f_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_472_ = crate::leanh::lean_ctor_get(v_inst_467_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_472_);
    v_toBind_473_ = crate::leanh::lean_ctor_get(v_inst_467_, 1);
    crate::leanh::lean_inc(v_toBind_473_);
    crate::leanh::lean_dec_ref(v_inst_467_);
    v_toPure_474_ = crate::leanh::lean_ctor_get(v_toApplicative_472_, 1);
    crate::leanh::lean_inc(v_toPure_474_);
    crate::leanh::lean_dec_ref(v_toApplicative_472_);
    v___f_475_ = crate::leanh::lean_alloc_closure(
        l_OptionT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_475_, 0, v_toPure_474_);
    crate::leanh::lean_closure_set(v___f_475_, 1, v_f_471_);
    v___x_476_ = crate::leanh::lean_apply_4(
        v_toBind_473_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_470_,
        v___f_475_,
    );
    return v___x_476_;
}
pub unsafe fn l_OptionT_pure___redArg(
    mut v_inst_477_: *mut crate::leanh::LeanObject,
    mut v_a_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_479_ = crate::leanh::lean_ctor_get(v_inst_477_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_479_);
    crate::leanh::lean_dec_ref(v_inst_477_);
    v_toPure_480_ = crate::leanh::lean_ctor_get(v_toApplicative_479_, 1);
    crate::leanh::lean_inc(v_toPure_480_);
    crate::leanh::lean_dec_ref(v_toApplicative_479_);
    v___x_481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_481_, 0, v_a_478_);
    v___x_482_ = crate::leanh::lean_apply_2(v_toPure_480_, crate::leanh::lean_box(0), v___x_481_);
    return v___x_482_;
}
pub unsafe fn l_OptionT_pure(
    mut v_m_483_: *mut crate::leanh::LeanObject,
    mut v_inst_484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_487_ = crate::leanh::lean_ctor_get(v_inst_484_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_487_);
    crate::leanh::lean_dec_ref(v_inst_484_);
    v_toPure_488_ = crate::leanh::lean_ctor_get(v_toApplicative_487_, 1);
    crate::leanh::lean_inc(v_toPure_488_);
    crate::leanh::lean_dec_ref(v_toApplicative_487_);
    v___x_489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_489_, 0, v_a_486_);
    v___x_490_ = crate::leanh::lean_apply_2(v_toPure_488_, crate::leanh::lean_box(0), v___x_489_);
    return v___x_490_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__0(
    mut v_toPure_491_: *mut crate::leanh::LeanObject,
    mut v_f_492_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_493_) == 0 {
                    crate::leanh::lean_dec(v_f_492_);
                    v___x_494_ = crate::leanh::lean_box(0);
                    v___x_495_ = crate::leanh::lean_apply_2(
                        v_toPure_491_,
                        crate::leanh::lean_box(0),
                        v___x_494_,
                    );
                    return v___x_495_;
                } else {
                    v_val_496_ = crate::leanh::lean_ctor_get(v_____do__lift_493_, 0);
                    v_isSharedCheck_505_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_493_)) as u8;
                    if v_isSharedCheck_505_ == 0 {
                        v___x_498_ = v_____do__lift_493_;
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_496_);
                        crate::leanh::lean_dec(v_____do__lift_493_);
                        v___x_498_ = crate::leanh::lean_box(0);
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_500_ = crate::leanh::lean_apply_1(v_f_492_, v_val_496_);
                if v_isShared_499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_498_, 0, v___x_500_);
                    v___x_502_ = v___x_498_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_500_);
                    v___x_502_ = v_reuseFailAlloc_504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_503_ = crate::leanh::lean_apply_2(
                    v_toPure_491_,
                    crate::leanh::lean_box(0),
                    v___x_502_,
                );
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__1(
    mut v_inst_506_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_507_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_508_: *mut crate::leanh::LeanObject,
    mut v_f_509_: *mut crate::leanh::LeanObject,
    mut v_x_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_511_ = crate::leanh::lean_ctor_get(v_inst_506_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_511_);
    v_toBind_512_ = crate::leanh::lean_ctor_get(v_inst_506_, 1);
    crate::leanh::lean_inc(v_toBind_512_);
    crate::leanh::lean_dec_ref(v_inst_506_);
    v_toPure_513_ = crate::leanh::lean_ctor_get(v_toApplicative_511_, 1);
    crate::leanh::lean_inc(v_toPure_513_);
    crate::leanh::lean_dec_ref(v_toApplicative_511_);
    v___f_514_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_514_, 0, v_toPure_513_);
    crate::leanh::lean_closure_set(v___f_514_, 1, v_f_509_);
    v___x_515_ = crate::leanh::lean_apply_4(
        v_toBind_512_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_510_,
        v___f_514_,
    );
    return v___x_515_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__2(
    mut v_toPure_516_: *mut crate::leanh::LeanObject,
    mut v___y_517_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut v_unused_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_518_) == 0 {
                    crate::leanh::lean_dec(v___y_517_);
                    v___x_519_ = crate::leanh::lean_box(0);
                    v___x_520_ = crate::leanh::lean_apply_2(
                        v_toPure_516_,
                        crate::leanh::lean_box(0),
                        v___x_519_,
                    );
                    return v___x_520_;
                } else {
                    v_isSharedCheck_528_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_518_)) as u8;
                    if v_isSharedCheck_528_ == 0 {
                        v_unused_529_ = crate::leanh::lean_ctor_get(v_____do__lift_518_, 0);
                        crate::leanh::lean_dec(v_unused_529_);
                        v___x_522_ = v_____do__lift_518_;
                        v_isShared_523_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_____do__lift_518_);
                        v___x_522_ = crate::leanh::lean_box(0);
                        v_isShared_523_ = v_isSharedCheck_528_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_522_, 0, v___y_517_);
                    v___x_525_ = v___x_522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_527_, 0, v___y_517_);
                    v___x_525_ = v_reuseFailAlloc_527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_526_ = crate::leanh::lean_apply_2(
                    v_toPure_516_,
                    crate::leanh::lean_box(0),
                    v___x_525_,
                );
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__3(
    mut v_inst_530_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_531_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_532_: *mut crate::leanh::LeanObject,
    mut v___y_533_: *mut crate::leanh::LeanObject,
    mut v___y_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_535_ = crate::leanh::lean_ctor_get(v_inst_530_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_535_);
    v_toBind_536_ = crate::leanh::lean_ctor_get(v_inst_530_, 1);
    crate::leanh::lean_inc(v_toBind_536_);
    crate::leanh::lean_dec_ref(v_inst_530_);
    v_toPure_537_ = crate::leanh::lean_ctor_get(v_toApplicative_535_, 1);
    crate::leanh::lean_inc(v_toPure_537_);
    crate::leanh::lean_dec_ref(v_toApplicative_535_);
    v___f_538_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_538_, 0, v_toPure_537_);
    crate::leanh::lean_closure_set(v___f_538_, 1, v___y_533_);
    v___x_539_ = crate::leanh::lean_apply_4(
        v_toBind_536_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___y_534_,
        v___f_538_,
    );
    return v___x_539_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__4(
    mut v_toPure_540_: *mut crate::leanh::LeanObject,
    mut v_val_541_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_542_) == 0 {
                    crate::leanh::lean_dec(v_val_541_);
                    v___x_543_ = crate::leanh::lean_box(0);
                    v___x_544_ = crate::leanh::lean_apply_2(
                        v_toPure_540_,
                        crate::leanh::lean_box(0),
                        v___x_543_,
                    );
                    return v___x_544_;
                } else {
                    v_val_545_ = crate::leanh::lean_ctor_get(v_____do__lift_542_, 0);
                    v_isSharedCheck_554_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_542_)) as u8;
                    if v_isSharedCheck_554_ == 0 {
                        v___x_547_ = v_____do__lift_542_;
                        v_isShared_548_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_545_);
                        crate::leanh::lean_dec(v_____do__lift_542_);
                        v___x_547_ = crate::leanh::lean_box(0);
                        v_isShared_548_ = v_isSharedCheck_554_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_549_ = crate::leanh::lean_apply_1(v_val_541_, v_val_545_);
                if v_isShared_548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_547_, 0, v___x_549_);
                    v___x_551_ = v___x_547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
                    v___x_551_ = v_reuseFailAlloc_553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_552_ = crate::leanh::lean_apply_2(
                    v_toPure_540_,
                    crate::leanh::lean_box(0),
                    v___x_551_,
                );
                return v___x_552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__5(
    mut v_toPure_555_: *mut crate::leanh::LeanObject,
    mut v_x_556_: *mut crate::leanh::LeanObject,
    mut v_toBind_557_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_558_) == 0 {
        let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_557_);
        crate::leanh::lean_dec(v_x_556_);
        v___x_559_ = crate::leanh::lean_box(0);
        v___x_560_ =
            crate::leanh::lean_apply_2(v_toPure_555_, crate::leanh::lean_box(0), v___x_559_);
        return v___x_560_;
    } else {
        let mut v_val_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_561_ = crate::leanh::lean_ctor_get(v_____do__lift_558_, 0);
        crate::leanh::lean_inc(v_val_561_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_558_, 1);
        v___f_562_ = crate::leanh::lean_alloc_closure(
            l_OptionT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_562_, 0, v_toPure_555_);
        crate::leanh::lean_closure_set(v___f_562_, 1, v_val_561_);
        v___x_563_ = crate::leanh::lean_box(0);
        v___x_564_ = crate::leanh::lean_apply_1(v_x_556_, v___x_563_);
        v___x_565_ = crate::leanh::lean_apply_4(
            v_toBind_557_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_564_,
            v___f_562_,
        );
        return v___x_565_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__6(
    mut v_inst_566_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_568_: *mut crate::leanh::LeanObject,
    mut v_f_569_: *mut crate::leanh::LeanObject,
    mut v_x_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_571_ = crate::leanh::lean_ctor_get(v_inst_566_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_571_);
    v_toBind_572_ = crate::leanh::lean_ctor_get(v_inst_566_, 1);
    crate::leanh::lean_inc_n(v_toBind_572_, 2);
    crate::leanh::lean_dec_ref(v_inst_566_);
    v_toPure_573_ = crate::leanh::lean_ctor_get(v_toApplicative_571_, 1);
    crate::leanh::lean_inc(v_toPure_573_);
    crate::leanh::lean_dec_ref(v_toApplicative_571_);
    v___f_574_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_574_, 0, v_toPure_573_);
    crate::leanh::lean_closure_set(v___f_574_, 1, v_x_570_);
    crate::leanh::lean_closure_set(v___f_574_, 2, v_toBind_572_);
    v___x_575_ = crate::leanh::lean_apply_4(
        v_toBind_572_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_569_,
        v___f_574_,
    );
    return v___x_575_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__7(
    mut v_toPure_576_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_577_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_578_) == 0 {
        let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_____do__lift_577_);
        v___x_579_ = crate::leanh::lean_box(0);
        v___x_580_ =
            crate::leanh::lean_apply_2(v_toPure_576_, crate::leanh::lean_box(0), v___x_579_);
        return v___x_580_;
    } else {
        let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_581_ = crate::leanh::lean_apply_2(
            v_toPure_576_,
            crate::leanh::lean_box(0),
            v_____do__lift_577_,
        );
        return v___x_581_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__7___boxed(
    mut v_toPure_582_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_583_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_585_ = l_OptionT_instMonad___redArg___lam__7(
        v_toPure_582_,
        v_____do__lift_583_,
        v_____do__lift_584_,
    );
    crate::leanh::lean_dec(v_____do__lift_584_);
    return v_res_585_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__8(
    mut v_toPure_586_: *mut crate::leanh::LeanObject,
    mut v_y_587_: *mut crate::leanh::LeanObject,
    mut v_toBind_588_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_589_) == 0 {
        let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_588_);
        crate::leanh::lean_dec(v_y_587_);
        v___x_590_ = crate::leanh::lean_apply_2(
            v_toPure_586_,
            crate::leanh::lean_box(0),
            v_____do__lift_589_,
        );
        return v___x_590_;
    } else {
        let mut v___f_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_591_ = crate::leanh::lean_alloc_closure(
            l_OptionT_instMonad___redArg___lam__7___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_591_, 0, v_toPure_586_);
        crate::leanh::lean_closure_set(v___f_591_, 1, v_____do__lift_589_);
        v___x_592_ = crate::leanh::lean_box(0);
        v___x_593_ = crate::leanh::lean_apply_1(v_y_587_, v___x_592_);
        v___x_594_ = crate::leanh::lean_apply_4(
            v_toBind_588_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_593_,
            v___f_591_,
        );
        return v___x_594_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__9(
    mut v_inst_595_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_596_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_597_: *mut crate::leanh::LeanObject,
    mut v_x_598_: *mut crate::leanh::LeanObject,
    mut v_y_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_600_ = crate::leanh::lean_ctor_get(v_inst_595_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_600_);
    v_toBind_601_ = crate::leanh::lean_ctor_get(v_inst_595_, 1);
    crate::leanh::lean_inc_n(v_toBind_601_, 2);
    crate::leanh::lean_dec_ref(v_inst_595_);
    v_toPure_602_ = crate::leanh::lean_ctor_get(v_toApplicative_600_, 1);
    crate::leanh::lean_inc(v_toPure_602_);
    crate::leanh::lean_dec_ref(v_toApplicative_600_);
    v___f_603_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_603_, 0, v_toPure_602_);
    crate::leanh::lean_closure_set(v___f_603_, 1, v_y_599_);
    crate::leanh::lean_closure_set(v___f_603_, 2, v_toBind_601_);
    v___x_604_ = crate::leanh::lean_apply_4(
        v_toBind_601_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_598_,
        v___f_603_,
    );
    return v___x_604_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__10(
    mut v_toPure_605_: *mut crate::leanh::LeanObject,
    mut v_y_606_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_607_) == 0 {
        let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_y_606_);
        v___x_608_ = crate::leanh::lean_box(0);
        v___x_609_ =
            crate::leanh::lean_apply_2(v_toPure_605_, crate::leanh::lean_box(0), v___x_608_);
        return v___x_609_;
    } else {
        let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_605_);
        v___x_610_ = crate::leanh::lean_box(0);
        v___x_611_ = crate::leanh::lean_apply_1(v_y_606_, v___x_610_);
        return v___x_611_;
    }
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__10___boxed(
    mut v_toPure_612_: *mut crate::leanh::LeanObject,
    mut v_y_613_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ =
        l_OptionT_instMonad___redArg___lam__10(v_toPure_612_, v_y_613_, v_____do__lift_614_);
    crate::leanh::lean_dec(v_____do__lift_614_);
    return v_res_615_;
}
pub unsafe fn l_OptionT_instMonad___redArg___lam__11(
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_617_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_618_: *mut crate::leanh::LeanObject,
    mut v_x_619_: *mut crate::leanh::LeanObject,
    mut v_y_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_621_ = crate::leanh::lean_ctor_get(v_inst_616_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_621_);
    v_toBind_622_ = crate::leanh::lean_ctor_get(v_inst_616_, 1);
    crate::leanh::lean_inc(v_toBind_622_);
    crate::leanh::lean_dec_ref(v_inst_616_);
    v_toPure_623_ = crate::leanh::lean_ctor_get(v_toApplicative_621_, 1);
    crate::leanh::lean_inc(v_toPure_623_);
    crate::leanh::lean_dec_ref(v_toApplicative_621_);
    v___f_624_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__10___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_624_, 0, v_toPure_623_);
    crate::leanh::lean_closure_set(v___f_624_, 1, v_y_620_);
    v___x_625_ = crate::leanh::lean_apply_4(
        v_toBind_622_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_619_,
        v___f_624_,
    );
    return v___x_625_;
}
pub unsafe fn l_OptionT_instMonad___redArg(
    mut v_inst_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_626_, 6);
    v___f_627_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_627_, 0, v_inst_626_);
    v___f_628_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_628_, 0, v_inst_626_);
    v___f_629_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_629_, 0, v_inst_626_);
    v___f_630_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_630_, 0, v_inst_626_);
    v___f_631_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_631_, 0, v_inst_626_);
    v___x_632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_632_, 0, v___f_627_);
    crate::leanh::lean_ctor_set(v___x_632_, 1, v___f_628_);
    v___x_633_ = crate::leanh::lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_633_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_633_, 1, v_inst_626_);
    v___x_634_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_634_, 0, v___x_632_);
    crate::leanh::lean_ctor_set(v___x_634_, 1, v___x_633_);
    crate::leanh::lean_ctor_set(v___x_634_, 2, v___f_629_);
    crate::leanh::lean_ctor_set(v___x_634_, 3, v___f_630_);
    crate::leanh::lean_ctor_set(v___x_634_, 4, v___f_631_);
    v___x_635_ = crate::leanh::lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___x_635_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_635_, 1, v_inst_626_);
    v___x_636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_634_);
    crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_635_);
    return v___x_636_;
}
pub unsafe fn l_OptionT_instMonad(
    mut v_m_637_: *mut crate::leanh::LeanObject,
    mut v_inst_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_638_, 6);
    v___f_639_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_639_, 0, v_inst_638_);
    v___f_640_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_640_, 0, v_inst_638_);
    v___f_641_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_641_, 0, v_inst_638_);
    v___f_642_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_642_, 0, v_inst_638_);
    v___f_643_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_643_, 0, v_inst_638_);
    v___x_644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_644_, 0, v___f_639_);
    crate::leanh::lean_ctor_set(v___x_644_, 1, v___f_640_);
    v___x_645_ = crate::leanh::lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_645_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_645_, 1, v_inst_638_);
    v___x_646_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_644_);
    crate::leanh::lean_ctor_set(v___x_646_, 1, v___x_645_);
    crate::leanh::lean_ctor_set(v___x_646_, 2, v___f_641_);
    crate::leanh::lean_ctor_set(v___x_646_, 3, v___f_642_);
    crate::leanh::lean_ctor_set(v___x_646_, 4, v___f_643_);
    v___x_647_ = crate::leanh::lean_alloc_closure(l_OptionT_bind as *mut core::ffi::c_void, 6, 2);
    crate::leanh::lean_closure_set(v___x_647_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_647_, 1, v_inst_638_);
    v___x_648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_648_, 0, v___x_646_);
    crate::leanh::lean_ctor_set(v___x_648_, 1, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l_OptionT_instInhabitedOfPure___redArg(
    mut v_inst_649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = crate::leanh::lean_box(0);
    v___x_651_ = crate::leanh::lean_apply_2(v_inst_649_, crate::leanh::lean_box(0), v___x_650_);
    return v___x_651_;
}
pub unsafe fn l_OptionT_instInhabitedOfPure(
    mut v_00_u03b1_652_: *mut crate::leanh::LeanObject,
    mut v_m_653_: *mut crate::leanh::LeanObject,
    mut v_inst_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_655_ = l_OptionT_instInhabitedOfPure___redArg(v_inst_654_);
    return v___x_655_;
}
pub unsafe fn l_OptionT_orElse___redArg___lam__0(
    mut v_y_656_: *mut crate::leanh::LeanObject,
    mut v_toPure_657_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_658_) == 0 {
        let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_657_);
        v___x_659_ = crate::leanh::lean_box(0);
        v___x_660_ = crate::leanh::lean_apply_1(v_y_656_, v___x_659_);
        return v___x_660_;
    } else {
        let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_y_656_);
        v___x_661_ = crate::leanh::lean_apply_2(
            v_toPure_657_,
            crate::leanh::lean_box(0),
            v_____do__lift_658_,
        );
        return v___x_661_;
    }
}
pub unsafe fn l_OptionT_orElse___redArg(
    mut v_inst_662_: *mut crate::leanh::LeanObject,
    mut v_x_663_: *mut crate::leanh::LeanObject,
    mut v_y_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_665_ = crate::leanh::lean_ctor_get(v_inst_662_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_665_);
    v_toBind_666_ = crate::leanh::lean_ctor_get(v_inst_662_, 1);
    crate::leanh::lean_inc(v_toBind_666_);
    crate::leanh::lean_dec_ref(v_inst_662_);
    v_toPure_667_ = crate::leanh::lean_ctor_get(v_toApplicative_665_, 1);
    crate::leanh::lean_inc(v_toPure_667_);
    crate::leanh::lean_dec_ref(v_toApplicative_665_);
    v___f_668_ = crate::leanh::lean_alloc_closure(
        l_OptionT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_668_, 0, v_y_664_);
    crate::leanh::lean_closure_set(v___f_668_, 1, v_toPure_667_);
    v___x_669_ = crate::leanh::lean_apply_4(
        v_toBind_666_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_663_,
        v___f_668_,
    );
    return v___x_669_;
}
pub unsafe fn l_OptionT_orElse(
    mut v_m_670_: *mut crate::leanh::LeanObject,
    mut v_inst_671_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_672_: *mut crate::leanh::LeanObject,
    mut v_x_673_: *mut crate::leanh::LeanObject,
    mut v_y_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_675_ = crate::leanh::lean_ctor_get(v_inst_671_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_675_);
    v_toBind_676_ = crate::leanh::lean_ctor_get(v_inst_671_, 1);
    crate::leanh::lean_inc(v_toBind_676_);
    crate::leanh::lean_dec_ref(v_inst_671_);
    v_toPure_677_ = crate::leanh::lean_ctor_get(v_toApplicative_675_, 1);
    crate::leanh::lean_inc(v_toPure_677_);
    crate::leanh::lean_dec_ref(v_toApplicative_675_);
    v___f_678_ = crate::leanh::lean_alloc_closure(
        l_OptionT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_678_, 0, v_y_674_);
    crate::leanh::lean_closure_set(v___f_678_, 1, v_toPure_677_);
    v___x_679_ = crate::leanh::lean_apply_4(
        v_toBind_676_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_673_,
        v___f_678_,
    );
    return v___x_679_;
}
pub unsafe fn l_OptionT_fail___redArg(
    mut v_inst_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_681_ = crate::leanh::lean_ctor_get(v_inst_680_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_681_);
    crate::leanh::lean_dec_ref(v_inst_680_);
    v_toPure_682_ = crate::leanh::lean_ctor_get(v_toApplicative_681_, 1);
    crate::leanh::lean_inc(v_toPure_682_);
    crate::leanh::lean_dec_ref(v_toApplicative_681_);
    v___x_683_ = crate::leanh::lean_box(0);
    v___x_684_ = crate::leanh::lean_apply_2(v_toPure_682_, crate::leanh::lean_box(0), v___x_683_);
    return v___x_684_;
}
pub unsafe fn l_OptionT_fail(
    mut v_m_685_: *mut crate::leanh::LeanObject,
    mut v_inst_686_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_688_ = crate::leanh::lean_ctor_get(v_inst_686_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_688_);
    crate::leanh::lean_dec_ref(v_inst_686_);
    v_toPure_689_ = crate::leanh::lean_ctor_get(v_toApplicative_688_, 1);
    crate::leanh::lean_inc(v_toPure_689_);
    crate::leanh::lean_dec_ref(v_toApplicative_688_);
    v___x_690_ = crate::leanh::lean_box(0);
    v___x_691_ = crate::leanh::lean_apply_2(v_toPure_689_, crate::leanh::lean_box(0), v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_OptionT_instAlternative___redArg(
    mut v_inst_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_inst_692_, 7);
    v___f_693_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_693_, 0, v_inst_692_);
    v___f_694_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_694_, 0, v_inst_692_);
    v___f_695_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__6 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_695_, 0, v_inst_692_);
    v___f_696_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_696_, 0, v_inst_692_);
    v___f_697_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonad___redArg___lam__11 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_697_, 0, v_inst_692_);
    v___x_698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_698_, 0, v___f_693_);
    crate::leanh::lean_ctor_set(v___x_698_, 1, v___f_694_);
    v___x_699_ = crate::leanh::lean_alloc_closure(l_OptionT_pure as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_699_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_699_, 1, v_inst_692_);
    v___x_700_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_700_, 0, v___x_698_);
    crate::leanh::lean_ctor_set(v___x_700_, 1, v___x_699_);
    crate::leanh::lean_ctor_set(v___x_700_, 2, v___f_695_);
    crate::leanh::lean_ctor_set(v___x_700_, 3, v___f_696_);
    crate::leanh::lean_ctor_set(v___x_700_, 4, v___f_697_);
    v___x_701_ = crate::leanh::lean_alloc_closure(l_OptionT_fail as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___x_701_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_701_, 1, v_inst_692_);
    v___x_702_ = crate::leanh::lean_alloc_closure(l_OptionT_orElse as *mut core::ffi::c_void, 5, 2);
    crate::leanh::lean_closure_set(v___x_702_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_702_, 1, v_inst_692_);
    v___x_703_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_700_);
    crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_701_);
    crate::leanh::lean_ctor_set(v___x_703_, 2, v___x_702_);
    return v___x_703_;
}
pub unsafe fn l_OptionT_instAlternative(
    mut v_m_704_: *mut crate::leanh::LeanObject,
    mut v_inst_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_OptionT_instAlternative___redArg(v_inst_705_);
    return v___x_706_;
}
pub unsafe fn l_OptionT_lift___redArg___lam__0(
    mut v_toPure_707_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_709_, 0, v_____do__lift_708_);
    v___x_710_ = crate::leanh::lean_apply_2(v_toPure_707_, crate::leanh::lean_box(0), v___x_709_);
    return v___x_710_;
}
pub unsafe fn l_OptionT_lift___redArg(
    mut v_inst_711_: *mut crate::leanh::LeanObject,
    mut v_x_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_713_ = crate::leanh::lean_ctor_get(v_inst_711_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_713_);
    v_toBind_714_ = crate::leanh::lean_ctor_get(v_inst_711_, 1);
    crate::leanh::lean_inc(v_toBind_714_);
    crate::leanh::lean_dec_ref(v_inst_711_);
    v_toPure_715_ = crate::leanh::lean_ctor_get(v_toApplicative_713_, 1);
    crate::leanh::lean_inc(v_toPure_715_);
    crate::leanh::lean_dec_ref(v_toApplicative_713_);
    v___f_716_ = crate::leanh::lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_716_, 0, v_toPure_715_);
    v___x_717_ = crate::leanh::lean_apply_4(
        v_toBind_714_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_712_,
        v___f_716_,
    );
    return v___x_717_;
}
pub unsafe fn l_OptionT_lift(
    mut v_m_718_: *mut crate::leanh::LeanObject,
    mut v_inst_719_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_720_: *mut crate::leanh::LeanObject,
    mut v_x_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_722_ = crate::leanh::lean_ctor_get(v_inst_719_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_722_);
    v_toBind_723_ = crate::leanh::lean_ctor_get(v_inst_719_, 1);
    crate::leanh::lean_inc(v_toBind_723_);
    crate::leanh::lean_dec_ref(v_inst_719_);
    v_toPure_724_ = crate::leanh::lean_ctor_get(v_toApplicative_722_, 1);
    crate::leanh::lean_inc(v_toPure_724_);
    crate::leanh::lean_dec_ref(v_toApplicative_722_);
    v___f_725_ = crate::leanh::lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_725_, 0, v_toPure_724_);
    v___x_726_ = crate::leanh::lean_apply_4(
        v_toBind_723_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_721_,
        v___f_725_,
    );
    return v___x_726_;
}
pub unsafe fn l_OptionT_instMonadLift___redArg(
    mut v_inst_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = crate::leanh::lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_728_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_728_, 1, v_inst_727_);
    return v___x_728_;
}
pub unsafe fn l_OptionT_instMonadLift(
    mut v_m_729_: *mut crate::leanh::LeanObject,
    mut v_inst_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = crate::leanh::lean_alloc_closure(l_OptionT_lift as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_731_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_731_, 1, v_inst_730_);
    return v___x_731_;
}
pub unsafe fn l_OptionT_instMonadFunctor___lam__0(
    mut v_00_u03b1_732_: *mut crate::leanh::LeanObject,
    mut v_f_733_: *mut crate::leanh::LeanObject,
    mut v_x_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = crate::leanh::lean_apply_2(v_f_733_, crate::leanh::lean_box(0), v_x_734_);
    return v___x_735_;
}
pub unsafe fn l_OptionT_instMonadFunctor(
    mut v_m_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_738_ = l_OptionT_instMonadFunctor___closed__0;
    return v___f_738_;
}
pub unsafe fn l_OptionT_tryCatch___redArg___lam__0(
    mut v_handle_739_: *mut crate::leanh::LeanObject,
    mut v_toPure_740_: *mut crate::leanh::LeanObject,
    mut v_____x_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_741_) == 0 {
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_740_);
        v___x_742_ = crate::leanh::lean_box(0);
        v___x_743_ = crate::leanh::lean_apply_1(v_handle_739_, v___x_742_);
        return v___x_743_;
    } else {
        let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_handle_739_);
        v___x_744_ =
            crate::leanh::lean_apply_2(v_toPure_740_, crate::leanh::lean_box(0), v_____x_741_);
        return v___x_744_;
    }
}
pub unsafe fn l_OptionT_tryCatch___redArg(
    mut v_inst_745_: *mut crate::leanh::LeanObject,
    mut v_x_746_: *mut crate::leanh::LeanObject,
    mut v_handle_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_748_ = crate::leanh::lean_ctor_get(v_inst_745_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_748_);
    v_toBind_749_ = crate::leanh::lean_ctor_get(v_inst_745_, 1);
    crate::leanh::lean_inc(v_toBind_749_);
    crate::leanh::lean_dec_ref(v_inst_745_);
    v_toPure_750_ = crate::leanh::lean_ctor_get(v_toApplicative_748_, 1);
    crate::leanh::lean_inc(v_toPure_750_);
    crate::leanh::lean_dec_ref(v_toApplicative_748_);
    v___f_751_ = crate::leanh::lean_alloc_closure(
        l_OptionT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_751_, 0, v_handle_747_);
    crate::leanh::lean_closure_set(v___f_751_, 1, v_toPure_750_);
    v___x_752_ = crate::leanh::lean_apply_4(
        v_toBind_749_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_746_,
        v___f_751_,
    );
    return v___x_752_;
}
pub unsafe fn l_OptionT_tryCatch(
    mut v_m_753_: *mut crate::leanh::LeanObject,
    mut v_inst_754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_755_: *mut crate::leanh::LeanObject,
    mut v_x_756_: *mut crate::leanh::LeanObject,
    mut v_handle_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_758_ = crate::leanh::lean_ctor_get(v_inst_754_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_758_);
    v_toBind_759_ = crate::leanh::lean_ctor_get(v_inst_754_, 1);
    crate::leanh::lean_inc(v_toBind_759_);
    crate::leanh::lean_dec_ref(v_inst_754_);
    v_toPure_760_ = crate::leanh::lean_ctor_get(v_toApplicative_758_, 1);
    crate::leanh::lean_inc(v_toPure_760_);
    crate::leanh::lean_dec_ref(v_toApplicative_758_);
    v___f_761_ = crate::leanh::lean_alloc_closure(
        l_OptionT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_761_, 0, v_handle_757_);
    crate::leanh::lean_closure_set(v___f_761_, 1, v_toPure_760_);
    v___x_762_ = crate::leanh::lean_apply_4(
        v_toBind_759_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_756_,
        v___f_761_,
    );
    return v___x_762_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit___redArg___lam__0(
    mut v_inst_763_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_764_: *mut crate::leanh::LeanObject,
    mut v_x_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_766_ = crate::leanh::lean_ctor_get(v_inst_763_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_766_);
    crate::leanh::lean_dec_ref(v_inst_763_);
    v_toPure_767_ = crate::leanh::lean_ctor_get(v_toApplicative_766_, 1);
    crate::leanh::lean_inc(v_toPure_767_);
    crate::leanh::lean_dec_ref(v_toApplicative_766_);
    v___x_768_ = crate::leanh::lean_box(0);
    v___x_769_ = crate::leanh::lean_apply_2(v_toPure_767_, crate::leanh::lean_box(0), v___x_768_);
    return v___x_769_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit___redArg(
    mut v_inst_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_770_);
    v___f_771_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonadExceptOfPUnit___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_771_, 0, v_inst_770_);
    v___x_772_ =
        crate::leanh::lean_alloc_closure(l_OptionT_tryCatch as *mut core::ffi::c_void, 5, 2);
    crate::leanh::lean_closure_set(v___x_772_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_772_, 1, v_inst_770_);
    v___x_773_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_773_, 0, v___f_771_);
    crate::leanh::lean_ctor_set(v___x_773_, 1, v___x_772_);
    return v___x_773_;
}
pub unsafe fn l_OptionT_instMonadExceptOfPUnit(
    mut v_m_774_: *mut crate::leanh::LeanObject,
    mut v_inst_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = l_OptionT_instMonadExceptOfPUnit___redArg(v_inst_775_);
    return v___x_776_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg___lam__0(
    mut v_inst_777_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_778_: *mut crate::leanh::LeanObject,
    mut v_e_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_780_ = crate::leanh::lean_ctor_get(v_inst_777_, 0);
    crate::leanh::lean_inc(v_throw_780_);
    crate::leanh::lean_dec_ref(v_inst_777_);
    v___x_781_ = crate::leanh::lean_apply_2(v_throw_780_, crate::leanh::lean_box(0), v_e_779_);
    return v___x_781_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg___lam__1(
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_783_: *mut crate::leanh::LeanObject,
    mut v_x_784_: *mut crate::leanh::LeanObject,
    mut v_handle_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_786_ = crate::leanh::lean_ctor_get(v_inst_782_, 1);
    crate::leanh::lean_inc(v_tryCatch_786_);
    crate::leanh::lean_dec_ref(v_inst_782_);
    v___x_787_ = crate::leanh::lean_apply_3(
        v_tryCatch_786_,
        crate::leanh::lean_box(0),
        v_x_784_,
        v_handle_785_,
    );
    return v___x_787_;
}
pub unsafe fn l_OptionT_instMonadExceptOf___redArg(
    mut v_inst_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_788_);
    v___f_789_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonadExceptOf___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_789_, 0, v_inst_788_);
    v___f_790_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_790_, 0, v_inst_788_);
    v___x_791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_791_, 0, v___f_789_);
    crate::leanh::lean_ctor_set(v___x_791_, 1, v___f_790_);
    return v___x_791_;
}
pub unsafe fn l_OptionT_instMonadExceptOf(
    mut v_m_792_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_793_: *mut crate::leanh::LeanObject,
    mut v_inst_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = l_OptionT_instMonadExceptOf___redArg(v_inst_794_);
    return v___x_795_;
}
pub unsafe fn l_OptionT_instMonadAttach___redArg___lam__0(
    mut v_x_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_796_) == 0 {
                    v___x_797_ = crate::leanh::lean_box(0);
                    return v___x_797_;
                } else {
                    v_val_798_ = crate::leanh::lean_ctor_get(v_x_796_, 0);
                    v_isSharedCheck_805_ = (!crate::leanh::lean_is_exclusive(v_x_796_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v_x_796_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_798_);
                        crate::leanh::lean_dec(v_x_796_);
                        v___x_800_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_798_);
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
    mut v_toFunctor_806_: *mut crate::leanh::LeanObject,
    mut v_inst_807_: *mut crate::leanh::LeanObject,
    mut v___f_808_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_809_: *mut crate::leanh::LeanObject,
    mut v_x_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_811_ = crate::leanh::lean_ctor_get(v_toFunctor_806_, 0);
    crate::leanh::lean_inc(v_map_811_);
    crate::leanh::lean_dec_ref(v_toFunctor_806_);
    v___x_812_ = crate::leanh::lean_apply_2(v_inst_807_, crate::leanh::lean_box(0), v_x_810_);
    v___x_813_ = crate::leanh::lean_apply_4(
        v_map_811_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_808_,
        v___x_812_,
    );
    return v___x_813_;
}
pub unsafe fn l_OptionT_instMonadAttach___redArg(
    mut v_inst_815_: *mut crate::leanh::LeanObject,
    mut v_inst_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_817_ = crate::leanh::lean_ctor_get(v_inst_815_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_817_);
    crate::leanh::lean_dec_ref(v_inst_815_);
    v_toFunctor_818_ = crate::leanh::lean_ctor_get(v_toApplicative_817_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_818_);
    crate::leanh::lean_dec_ref(v_toApplicative_817_);
    v___f_819_ = l_OptionT_instMonadAttach___redArg___closed__0;
    v___f_820_ = crate::leanh::lean_alloc_closure(
        l_OptionT_instMonadAttach___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_820_, 0, v_toFunctor_818_);
    crate::leanh::lean_closure_set(v___f_820_, 1, v_inst_816_);
    crate::leanh::lean_closure_set(v___f_820_, 2, v___f_819_);
    return v___f_820_;
}
pub unsafe fn l_OptionT_instMonadAttach(
    mut v_m_821_: *mut crate::leanh::LeanObject,
    mut v_inst_822_: *mut crate::leanh::LeanObject,
    mut v_inst_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l_OptionT_instMonadAttach___redArg(v_inst_822_, v_inst_823_);
    return v___x_824_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__0(
    mut v_00_u03b2_825_: *mut crate::leanh::LeanObject,
    mut v_x_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_826_);
    return v_x_826_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__0___boxed(
    mut v_00_u03b2_827_: *mut crate::leanh::LeanObject,
    mut v_x_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_829_ = l_instMonadControlOptionTOfMonad___redArg___lam__0(v_00_u03b2_827_, v_x_828_);
    crate::leanh::lean_dec(v_x_828_);
    return v_res_829_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__2(
    mut v_inst_830_: *mut crate::leanh::LeanObject,
    mut v___f_831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_832_: *mut crate::leanh::LeanObject,
    mut v_f_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_834_ = crate::leanh::lean_ctor_get(v_inst_830_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_834_);
    v_toBind_835_ = crate::leanh::lean_ctor_get(v_inst_830_, 1);
    crate::leanh::lean_inc(v_toBind_835_);
    crate::leanh::lean_dec_ref(v_inst_830_);
    v_toPure_836_ = crate::leanh::lean_ctor_get(v_toApplicative_834_, 1);
    crate::leanh::lean_inc(v_toPure_836_);
    crate::leanh::lean_dec_ref(v_toApplicative_834_);
    v___x_837_ = crate::leanh::lean_apply_1(v_f_833_, v___f_831_);
    v___f_838_ = crate::leanh::lean_alloc_closure(
        l_OptionT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_838_, 0, v_toPure_836_);
    v___x_839_ = crate::leanh::lean_apply_4(
        v_toBind_835_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_837_,
        v___f_838_,
    );
    return v___x_839_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__1(
    mut v_00_u03b1_840_: *mut crate::leanh::LeanObject,
    mut v_x_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_841_);
    return v_x_841_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg___lam__1___boxed(
    mut v_00_u03b1_842_: *mut crate::leanh::LeanObject,
    mut v_x_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_instMonadControlOptionTOfMonad___redArg___lam__1(v_00_u03b1_842_, v_x_843_);
    crate::leanh::lean_dec(v_x_843_);
    return v_res_844_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad___redArg(
    mut v_inst_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_848_ = l_instMonadControlOptionTOfMonad___redArg___closed__0;
    v___f_849_ = crate::leanh::lean_alloc_closure(
        l_instMonadControlOptionTOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_849_, 0, v_inst_847_);
    crate::leanh::lean_closure_set(v___f_849_, 1, v___f_848_);
    v___f_850_ = l_instMonadControlOptionTOfMonad___redArg___closed__1;
    v___x_851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_851_, 0, v___f_849_);
    crate::leanh::lean_ctor_set(v___x_851_, 1, v___f_850_);
    return v___x_851_;
}
pub unsafe fn l_instMonadControlOptionTOfMonad(
    mut v_m_852_: *mut crate::leanh::LeanObject,
    mut v_inst_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_instMonadControlOptionTOfMonad___redArg(v_inst_853_);
    return v___x_854_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Option(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_MonadAttach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Option(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Option(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_MonadAttach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Option(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Control_Option(builtin);
}
