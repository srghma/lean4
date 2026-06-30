// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: Lean.Util.FindExpr Lean.Declaration
use crate::ffi::{lean_find_expr, lean_nat_dec_le, lean_nat_sub};
use crate::r#gen::Lean::Declaration::{
    initialize_Lean_Declaration, runtime_initialize_Lean_Declaration,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Util::FindExpr::{
    initialize_Lean_Util_FindExpr, runtime_initialize_Lean_Util_FindExpr,
};
pub static l_Lean_Expr_isSorry___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [115, 111, 114, 114, 121, 65, 120, 0],
    };
static mut l_Lean_Expr_isSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_isSorry___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__0_value)
                as *mut leanh::LeanObject,
            5207765522374246084 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isSorry___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_isSyntheticSorry___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Expr_isSyntheticSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Expr_isSyntheticSorry___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Expr_isSyntheticSorry___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_isSyntheticSorry___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__1_value)
                as *mut leanh::LeanObject,
            9255189395584251158 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isSyntheticSorry___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Expr_isNonSyntheticSorry___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Expr_isNonSyntheticSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
                as *mut leanh::LeanObject,
            12882480457794858234 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_isNonSyntheticSorry___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__0_value)
                as *mut leanh::LeanObject,
            15761733860085307253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isNonSyntheticSorry___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Expr_hasSorry___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Expr_hasSorry___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasSorry___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Expr_hasSyntheticSorry___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Expr_isSyntheticSorry___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasSyntheticSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasSyntheticSorry___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Expr_hasNonSyntheticSorry___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Expr_isNonSyntheticSorry___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasNonSyntheticSorry___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasNonSyntheticSorry___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Expr_isSorry(mut v_e_421_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    v___x_422_ = l_Lean_Expr_isSorry___closed__1;
    v___x_423_ = l_Lean_Expr_isAppOf(v_e_421_, v___x_422_);
    return v___x_423_;
}
pub unsafe fn l_Lean_Expr_isSorry___boxed(
    mut v_e_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_425_: u8 = 0;
    let mut v_r_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Lean_Expr_isSorry(v_e_424_);
    leanh::lean_dec_ref(v_e_424_);
    v_r_426_ = leanh::lean_box((v_res_425_) as usize);
    return v_r_426_;
}
pub unsafe fn l_Lean_Expr_isSyntheticSorry(mut v_e_432_: *mut leanh::LeanObject) -> u8 {
    let mut v___y_434_: u8 = 0;
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_442_ = l_Lean_Expr_isSorry___closed__1;
                v___x_443_ = l_Lean_Expr_isAppOf(v_e_432_, v___x_442_);
                if v___x_443_ == 0 {
                    v___y_434_ = v___x_443_;
                    state = 1;
                    continue;
                } else {
                    v___x_444_ = leanh::lean_unsigned_to_nat(2);
                    v___x_445_ = l_Lean_Expr_getAppNumArgs(v_e_432_);
                    v___x_446_ = lean_nat_dec_le(v___x_444_, v___x_445_);
                    leanh::lean_dec(v___x_445_);
                    v___y_434_ = v___x_446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_434_ == 0 {
                    return v___y_434_;
                } else {
                    v___x_435_ = leanh::lean_unsigned_to_nat(1);
                    v___x_436_ = l_Lean_Expr_getAppNumArgs(v_e_432_);
                    v___x_437_ = lean_nat_sub(v___x_436_, v___x_435_);
                    leanh::lean_dec(v___x_436_);
                    v___x_438_ = lean_nat_sub(v___x_437_, v___x_435_);
                    leanh::lean_dec(v___x_437_);
                    v___x_439_ = l_Lean_Expr_getRevArg_x21(v_e_432_, v___x_438_);
                    v___x_440_ = l_Lean_Expr_isSyntheticSorry___closed__2;
                    v___x_441_ = l_Lean_Expr_isConstOf(v___x_439_, v___x_440_);
                    leanh::lean_dec_ref(v___x_439_);
                    return v___x_441_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_isSyntheticSorry___boxed(
    mut v_e_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_448_: u8 = 0;
    let mut v_r_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Lean_Expr_isSyntheticSorry(v_e_447_);
    leanh::lean_dec_ref(v_e_447_);
    v_r_449_ = leanh::lean_box((v_res_448_) as usize);
    return v_r_449_;
}
pub unsafe fn l_Lean_Expr_isNonSyntheticSorry(mut v_e_454_: *mut leanh::LeanObject) -> u8 {
    let mut v___y_456_: u8 = 0;
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_464_ = l_Lean_Expr_isSorry___closed__1;
                v___x_465_ = l_Lean_Expr_isAppOf(v_e_454_, v___x_464_);
                if v___x_465_ == 0 {
                    v___y_456_ = v___x_465_;
                    state = 1;
                    continue;
                } else {
                    v___x_466_ = leanh::lean_unsigned_to_nat(2);
                    v___x_467_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
                    v___x_468_ = lean_nat_dec_le(v___x_466_, v___x_467_);
                    leanh::lean_dec(v___x_467_);
                    v___y_456_ = v___x_468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_456_ == 0 {
                    return v___y_456_;
                } else {
                    v___x_457_ = leanh::lean_unsigned_to_nat(1);
                    v___x_458_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
                    v___x_459_ = lean_nat_sub(v___x_458_, v___x_457_);
                    leanh::lean_dec(v___x_458_);
                    v___x_460_ = lean_nat_sub(v___x_459_, v___x_457_);
                    leanh::lean_dec(v___x_459_);
                    v___x_461_ = l_Lean_Expr_getRevArg_x21(v_e_454_, v___x_460_);
                    v___x_462_ = l_Lean_Expr_isNonSyntheticSorry___closed__1;
                    v___x_463_ = l_Lean_Expr_isConstOf(v___x_461_, v___x_462_);
                    leanh::lean_dec_ref(v___x_461_);
                    return v___x_463_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_isNonSyntheticSorry___boxed(
    mut v_e_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_470_: u8 = 0;
    let mut v_r_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lean_Expr_isNonSyntheticSorry(v_e_469_);
    leanh::lean_dec_ref(v_e_469_);
    v_r_471_ = leanh::lean_box((v_res_470_) as usize);
    return v_r_471_;
}
pub unsafe fn l_Lean_Expr_hasSorry___lam__0(mut v_x_472_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: u8 = 0;
    v___x_473_ = l_Lean_Expr_isSorry___closed__1;
    v___x_474_ = l_Lean_Expr_isConstOf(v_x_472_, v___x_473_);
    return v___x_474_;
}
pub unsafe fn l_Lean_Expr_hasSorry___lam__0___boxed(
    mut v_x_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_476_: u8 = 0;
    let mut v_r_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Expr_hasSorry___lam__0(v_x_475_);
    leanh::lean_dec_ref(v_x_475_);
    v_r_477_ = leanh::lean_box((v_res_476_) as usize);
    return v_r_477_;
}
pub unsafe fn l_Lean_Expr_hasSorry(mut v_e_479_: *mut leanh::LeanObject) -> u8 {
    let mut v___f_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_480_ = l_Lean_Expr_hasSorry___closed__0;
    v___x_481_ = lean_find_expr(v___f_480_, v_e_479_);
    if leanh::lean_obj_tag(v___x_481_) == 0 {
        let mut v___x_482_: u8 = 0;
        v___x_482_ = 0;
        return v___x_482_;
    } else {
        let mut v___x_483_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_481_, 1);
        v___x_483_ = 1;
        return v___x_483_;
    }
}
pub unsafe fn l_Lean_Expr_hasSorry___boxed(
    mut v_e_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_485_: u8 = 0;
    let mut v_r_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_485_ = l_Lean_Expr_hasSorry(v_e_484_);
    leanh::lean_dec_ref(v_e_484_);
    v_r_486_ = leanh::lean_box((v_res_485_) as usize);
    return v_r_486_;
}
pub unsafe fn l_Lean_Expr_hasSyntheticSorry(mut v_e_488_: *mut leanh::LeanObject) -> u8 {
    let mut v___f_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_489_ = l_Lean_Expr_hasSyntheticSorry___closed__0;
    v___x_490_ = lean_find_expr(v___f_489_, v_e_488_);
    if leanh::lean_obj_tag(v___x_490_) == 0 {
        let mut v___x_491_: u8 = 0;
        v___x_491_ = 0;
        return v___x_491_;
    } else {
        let mut v___x_492_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_490_, 1);
        v___x_492_ = 1;
        return v___x_492_;
    }
}
pub unsafe fn l_Lean_Expr_hasSyntheticSorry___boxed(
    mut v_e_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_494_: u8 = 0;
    let mut v_r_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lean_Expr_hasSyntheticSorry(v_e_493_);
    leanh::lean_dec_ref(v_e_493_);
    v_r_495_ = leanh::lean_box((v_res_494_) as usize);
    return v_r_495_;
}
pub unsafe fn l_Lean_Expr_hasNonSyntheticSorry(mut v_e_497_: *mut leanh::LeanObject) -> u8 {
    let mut v___f_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_498_ = l_Lean_Expr_hasNonSyntheticSorry___closed__0;
    v___x_499_ = lean_find_expr(v___f_498_, v_e_497_);
    if leanh::lean_obj_tag(v___x_499_) == 0 {
        let mut v___x_500_: u8 = 0;
        v___x_500_ = 0;
        return v___x_500_;
    } else {
        let mut v___x_501_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_499_, 1);
        v___x_501_ = 1;
        return v___x_501_;
    }
}
pub unsafe fn l_Lean_Expr_hasNonSyntheticSorry___boxed(
    mut v_e_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_503_: u8 = 0;
    let mut v_r_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_502_);
    leanh::lean_dec_ref(v_e_502_);
    v_r_504_ = leanh::lean_box((v_res_503_) as usize);
    return v_r_504_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
    mut v_r_505_: u8,
    mut v_e_506_: *mut leanh::LeanObject,
) -> u8 {
    if v_r_505_ == 0 {
        let mut v___x_507_: u8 = 0;
        v___x_507_ = l_Lean_Expr_hasSorry(v_e_506_);
        return v___x_507_;
    } else {
        return v_r_505_;
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(
    mut v_r_508_: *mut leanh::LeanObject,
    mut v_e_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_boxed_510_: u8 = 0;
    let mut v_res_511_: u8 = 0;
    let mut v_r_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_510_ = (leanh::lean_unbox(v_r_508_) as u8);
    v_res_511_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
        v_r_boxed_510_,
        v_e_509_,
    );
    leanh::lean_dec_ref(v_e_509_);
    v_r_512_ = leanh::lean_box((v_res_511_) as usize);
    return v_r_512_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(
    mut v_x_513_: u8,
    mut v_x_514_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_514_) == 0 {
                    return v_x_513_;
                } else {
                    v_head_515_ = leanh::lean_ctor_get(v_x_514_, 0);
                    v_toConstantVal_516_ = leanh::lean_ctor_get(v_head_515_, 0);
                    v_tail_517_ = leanh::lean_ctor_get(v_x_514_, 1);
                    v_value_518_ = leanh::lean_ctor_get(v_head_515_, 1);
                    v_type_519_ = leanh::lean_ctor_get(v_toConstantVal_516_, 2);
                    v___x_520_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_x_513_, v_type_519_);
                    v___x_521_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_520_, v_value_518_);
                    v_x_513_ = v___x_521_;
                    v_x_514_ = v_tail_517_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(
    mut v_x_523_: *mut leanh::LeanObject,
    mut v_x_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1024__boxed_525_: u8 = 0;
    let mut v_res_526_: u8 = 0;
    let mut v_r_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_525_ = (leanh::lean_unbox(v_x_523_) as u8);
    v_res_526_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_1024__boxed_525_, v_x_524_);
    leanh::lean_dec(v_x_524_);
    v_r_527_ = leanh::lean_box((v_res_526_) as usize);
    return v_r_527_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(
    mut v_x_528_: u8,
    mut v_x_529_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v_tail_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_529_) == 0 {
                    return v_x_528_;
                } else {
                    if v_x_528_ == 0 {
                        v_head_530_ = leanh::lean_ctor_get(v_x_529_, 0);
                        v_tail_531_ = leanh::lean_ctor_get(v_x_529_, 1);
                        v_type_532_ = leanh::lean_ctor_get(v_head_530_, 1);
                        v___x_533_ = l_Lean_Expr_hasSorry(v_type_532_);
                        v_x_528_ = v___x_533_;
                        v_x_529_ = v_tail_531_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_535_ = leanh::lean_ctor_get(v_x_529_, 1);
                        v_x_529_ = v_tail_535_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_x_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1040__boxed_539_: u8 = 0;
    let mut v_res_540_: u8 = 0;
    let mut v_r_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_539_ = (leanh::lean_unbox(v_x_537_) as u8);
    v_res_540_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_539_, v_x_538_);
    leanh::lean_dec(v_x_538_);
    v_r_541_ = leanh::lean_box((v_res_540_) as usize);
    return v_r_541_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(
    mut v_x_542_: u8,
    mut v_x_543_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_543_) == 0 {
        return v_x_542_;
    } else {
        if v_x_542_ == 0 {
            let mut v_head_544_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_545_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_546_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_547_: u8 = 0;
            let mut v___x_548_: u8 = 0;
            v_head_544_ = leanh::lean_ctor_get(v_x_543_, 0);
            v_tail_545_ = leanh::lean_ctor_get(v_x_543_, 1);
            v_type_546_ = leanh::lean_ctor_get(v_head_544_, 1);
            v___x_547_ = l_Lean_Expr_hasSorry(v_type_546_);
            v___x_548_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v___x_547_, v_tail_545_);
            return v___x_548_;
        } else {
            let mut v_tail_549_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_550_: u8 = 0;
            v_tail_549_ = leanh::lean_ctor_get(v_x_543_, 1);
            v___x_550_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_542_, v_tail_549_);
            return v___x_550_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(
    mut v_x_551_: *mut leanh::LeanObject,
    mut v_x_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1058__boxed_553_: u8 = 0;
    let mut v_res_554_: u8 = 0;
    let mut v_r_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_553_ = (leanh::lean_unbox(v_x_551_) as u8);
    v_res_554_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_1058__boxed_553_, v_x_552_);
    leanh::lean_dec(v_x_552_);
    v_r_555_ = leanh::lean_box((v_res_554_) as usize);
    return v_r_555_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(
    mut v_x_556_: u8,
    mut v_x_557_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_563_: u8 = 0;
    let mut v___x_564_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_557_) == 0 {
                    return v_x_556_;
                } else {
                    v_head_558_ = leanh::lean_ctor_get(v_x_557_, 0);
                    v_tail_559_ = leanh::lean_ctor_get(v_x_557_, 1);
                    v_type_560_ = leanh::lean_ctor_get(v_head_558_, 1);
                    v_ctors_561_ = leanh::lean_ctor_get(v_head_558_, 2);
                    if v_x_556_ == 0 {
                        v___x_566_ = l_Lean_Expr_hasSorry(v_type_560_);
                        v___y_563_ = v___x_566_;
                        state = 1;
                        continue;
                    } else {
                        v___y_563_ = v_x_556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_564_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_563_, v_ctors_561_);
                v_x_556_ = v___x_564_;
                v_x_557_ = v_tail_559_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(
    mut v_x_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1076__boxed_569_: u8 = 0;
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_569_ = (leanh::lean_unbox(v_x_567_) as u8);
    v_res_570_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_569_, v_x_568_);
    leanh::lean_dec(v_x_568_);
    v_r_571_ = leanh::lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(
    mut v_x_572_: u8,
    mut v_x_573_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_579_: u8 = 0;
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_573_) == 0 {
                    return v_x_572_;
                } else {
                    v_head_574_ = leanh::lean_ctor_get(v_x_573_, 0);
                    v_tail_575_ = leanh::lean_ctor_get(v_x_573_, 1);
                    v_type_576_ = leanh::lean_ctor_get(v_head_574_, 1);
                    v_ctors_577_ = leanh::lean_ctor_get(v_head_574_, 2);
                    if v_x_572_ == 0 {
                        v___x_582_ = l_Lean_Expr_hasSorry(v_type_576_);
                        v___y_579_ = v___x_582_;
                        state = 1;
                        continue;
                    } else {
                        v___y_579_ = v_x_572_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_580_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_579_, v_ctors_577_);
                v___x_581_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v___x_580_, v_tail_575_);
                return v___x_581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(
    mut v_x_583_: *mut leanh::LeanObject,
    mut v_x_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1096__boxed_585_: u8 = 0;
    let mut v_res_586_: u8 = 0;
    let mut v_r_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_585_ = (leanh::lean_unbox(v_x_583_) as u8);
    v_res_586_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_1096__boxed_585_, v_x_584_);
    leanh::lean_dec(v_x_584_);
    v_r_587_ = leanh::lean_box((v_res_586_) as usize);
    return v_r_587_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
    mut v_d_588_: *mut leanh::LeanObject,
    mut v_a_589_: u8,
) -> u8 {
    match leanh::lean_obj_tag(v_d_588_) {
        0 => {
            let mut v_val_590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_591_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_593_: u8 = 0;
            v_val_590_ = leanh::lean_ctor_get(v_d_588_, 0);
            v_toConstantVal_591_ = leanh::lean_ctor_get(v_val_590_, 0);
            v_type_592_ = leanh::lean_ctor_get(v_toConstantVal_591_, 2);
            v___x_593_ =
                l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
                    v_a_589_,
                    v_type_592_,
                );
            return v___x_593_;
        }
        4 => {
            return v_a_589_;
        }
        5 => {
            let mut v_defns_594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_595_: u8 = 0;
            v_defns_594_ = leanh::lean_ctor_get(v_d_588_, 0);
            v___x_595_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_a_589_, v_defns_594_);
            return v___x_595_;
        }
        6 => {
            let mut v_types_596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_597_: u8 = 0;
            v_types_596_ = leanh::lean_ctor_get(v_d_588_, 2);
            v___x_597_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_a_589_, v_types_596_);
            return v___x_597_;
        }
        _ => {
            let mut v_val_598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_599_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_600_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_601_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_602_: u8 = 0;
            let mut v___x_603_: u8 = 0;
            v_val_598_ = leanh::lean_ctor_get(v_d_588_, 0);
            v_toConstantVal_599_ = leanh::lean_ctor_get(v_val_598_, 0);
            v_value_600_ = leanh::lean_ctor_get(v_val_598_, 1);
            v_type_601_ = leanh::lean_ctor_get(v_toConstantVal_599_, 2);
            v___x_602_ =
                l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
                    v_a_589_,
                    v_type_601_,
                );
            v___x_603_ =
                l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
                    v___x_602_,
                    v_value_600_,
                );
            return v___x_603_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(
    mut v_d_604_: *mut leanh::LeanObject,
    mut v_a_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_606_: u8 = 0;
    let mut v_res_607_: u8 = 0;
    let mut v_r_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_606_ = (leanh::lean_unbox(v_a_605_) as u8);
    v_res_607_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
        v_d_604_,
        v_a_boxed_606_,
    );
    leanh::lean_dec(v_d_604_);
    v_r_608_ = leanh::lean_box((v_res_607_) as usize);
    return v_r_608_;
}
pub unsafe fn l_Lean_Declaration_hasSorry(mut v_d_609_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_610_: u8 = 0;
    let mut v___x_611_: u8 = 0;
    v___x_610_ = 0;
    v___x_611_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
        v_d_609_, v___x_610_,
    );
    return v___x_611_;
}
pub unsafe fn l_Lean_Declaration_hasSorry___boxed(
    mut v_d_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_613_: u8 = 0;
    let mut v_r_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_613_ = l_Lean_Declaration_hasSorry(v_d_612_);
    leanh::lean_dec(v_d_612_);
    v_r_614_ = leanh::lean_box((v_res_613_) as usize);
    return v_r_614_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(
    mut v_r_615_: u8,
    mut v_e_616_: *mut leanh::LeanObject,
) -> u8 {
    if v_r_615_ == 0 {
        let mut v___x_617_: u8 = 0;
        v___x_617_ = l_Lean_Expr_hasSyntheticSorry(v_e_616_);
        return v___x_617_;
    } else {
        return v_r_615_;
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(
    mut v_r_618_: *mut leanh::LeanObject,
    mut v_e_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_boxed_620_: u8 = 0;
    let mut v_res_621_: u8 = 0;
    let mut v_r_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_620_ = (leanh::lean_unbox(v_r_618_) as u8);
    v_res_621_ =
        l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(
            v_r_boxed_620_,
            v_e_619_,
        );
    leanh::lean_dec_ref(v_e_619_);
    v_r_622_ = leanh::lean_box((v_res_621_) as usize);
    return v_r_622_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(
    mut v_x_623_: u8,
    mut v_x_624_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_624_) == 0 {
                    return v_x_623_;
                } else {
                    v_head_625_ = leanh::lean_ctor_get(v_x_624_, 0);
                    v_toConstantVal_626_ = leanh::lean_ctor_get(v_head_625_, 0);
                    v_tail_627_ = leanh::lean_ctor_get(v_x_624_, 1);
                    v_value_628_ = leanh::lean_ctor_get(v_head_625_, 1);
                    v_type_629_ = leanh::lean_ctor_get(v_toConstantVal_626_, 2);
                    v___x_630_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_x_623_, v_type_629_);
                    v___x_631_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_630_, v_value_628_);
                    v_x_623_ = v___x_631_;
                    v_x_624_ = v_tail_627_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(
    mut v_x_633_: *mut leanh::LeanObject,
    mut v_x_634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1024__boxed_635_: u8 = 0;
    let mut v_res_636_: u8 = 0;
    let mut v_r_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_635_ = (leanh::lean_unbox(v_x_633_) as u8);
    v_res_636_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_635_, v_x_634_);
    leanh::lean_dec(v_x_634_);
    v_r_637_ = leanh::lean_box((v_res_636_) as usize);
    return v_r_637_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(
    mut v_x_638_: u8,
    mut v_x_639_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v_tail_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_639_) == 0 {
                    return v_x_638_;
                } else {
                    if v_x_638_ == 0 {
                        v_head_640_ = leanh::lean_ctor_get(v_x_639_, 0);
                        v_tail_641_ = leanh::lean_ctor_get(v_x_639_, 1);
                        v_type_642_ = leanh::lean_ctor_get(v_head_640_, 1);
                        v___x_643_ = l_Lean_Expr_hasSyntheticSorry(v_type_642_);
                        v_x_638_ = v___x_643_;
                        v_x_639_ = v_tail_641_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_645_ = leanh::lean_ctor_get(v_x_639_, 1);
                        v_x_639_ = v_tail_645_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(
    mut v_x_647_: *mut leanh::LeanObject,
    mut v_x_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1040__boxed_649_: u8 = 0;
    let mut v_res_650_: u8 = 0;
    let mut v_r_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_649_ = (leanh::lean_unbox(v_x_647_) as u8);
    v_res_650_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_649_, v_x_648_);
    leanh::lean_dec(v_x_648_);
    v_r_651_ = leanh::lean_box((v_res_650_) as usize);
    return v_r_651_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(
    mut v_x_652_: u8,
    mut v_x_653_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_653_) == 0 {
        return v_x_652_;
    } else {
        if v_x_652_ == 0 {
            let mut v_head_654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_655_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_656_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_657_: u8 = 0;
            let mut v___x_658_: u8 = 0;
            v_head_654_ = leanh::lean_ctor_get(v_x_653_, 0);
            v_tail_655_ = leanh::lean_ctor_get(v_x_653_, 1);
            v_type_656_ = leanh::lean_ctor_get(v_head_654_, 1);
            v___x_657_ = l_Lean_Expr_hasSyntheticSorry(v_type_656_);
            v___x_658_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v___x_657_, v_tail_655_);
            return v___x_658_;
        } else {
            let mut v_tail_659_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_660_: u8 = 0;
            v_tail_659_ = leanh::lean_ctor_get(v_x_653_, 1);
            v___x_660_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_652_, v_tail_659_);
            return v___x_660_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(
    mut v_x_661_: *mut leanh::LeanObject,
    mut v_x_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1058__boxed_663_: u8 = 0;
    let mut v_res_664_: u8 = 0;
    let mut v_r_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_663_ = (leanh::lean_unbox(v_x_661_) as u8);
    v_res_664_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_663_, v_x_662_);
    leanh::lean_dec(v_x_662_);
    v_r_665_ = leanh::lean_box((v_res_664_) as usize);
    return v_r_665_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(
    mut v_x_666_: u8,
    mut v_x_667_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_673_: u8 = 0;
    let mut v___x_674_: u8 = 0;
    let mut v___x_676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_667_) == 0 {
                    return v_x_666_;
                } else {
                    v_head_668_ = leanh::lean_ctor_get(v_x_667_, 0);
                    v_tail_669_ = leanh::lean_ctor_get(v_x_667_, 1);
                    v_type_670_ = leanh::lean_ctor_get(v_head_668_, 1);
                    v_ctors_671_ = leanh::lean_ctor_get(v_head_668_, 2);
                    if v_x_666_ == 0 {
                        v___x_676_ = l_Lean_Expr_hasSyntheticSorry(v_type_670_);
                        v___y_673_ = v___x_676_;
                        state = 1;
                        continue;
                    } else {
                        v___y_673_ = v_x_666_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_674_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_673_, v_ctors_671_);
                v_x_666_ = v___x_674_;
                v_x_667_ = v_tail_669_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(
    mut v_x_677_: *mut leanh::LeanObject,
    mut v_x_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1076__boxed_679_: u8 = 0;
    let mut v_res_680_: u8 = 0;
    let mut v_r_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_679_ = (leanh::lean_unbox(v_x_677_) as u8);
    v_res_680_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_679_, v_x_678_);
    leanh::lean_dec(v_x_678_);
    v_r_681_ = leanh::lean_box((v_res_680_) as usize);
    return v_r_681_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(
    mut v_x_682_: u8,
    mut v_x_683_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_689_: u8 = 0;
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_683_) == 0 {
                    return v_x_682_;
                } else {
                    v_head_684_ = leanh::lean_ctor_get(v_x_683_, 0);
                    v_tail_685_ = leanh::lean_ctor_get(v_x_683_, 1);
                    v_type_686_ = leanh::lean_ctor_get(v_head_684_, 1);
                    v_ctors_687_ = leanh::lean_ctor_get(v_head_684_, 2);
                    if v_x_682_ == 0 {
                        v___x_692_ = l_Lean_Expr_hasSyntheticSorry(v_type_686_);
                        v___y_689_ = v___x_692_;
                        state = 1;
                        continue;
                    } else {
                        v___y_689_ = v_x_682_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_690_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_689_, v_ctors_687_);
                v___x_691_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v___x_690_, v_tail_685_);
                return v___x_691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(
    mut v_x_693_: *mut leanh::LeanObject,
    mut v_x_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1096__boxed_695_: u8 = 0;
    let mut v_res_696_: u8 = 0;
    let mut v_r_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_695_ = (leanh::lean_unbox(v_x_693_) as u8);
    v_res_696_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_695_, v_x_694_);
    leanh::lean_dec(v_x_694_);
    v_r_697_ = leanh::lean_box((v_res_696_) as usize);
    return v_r_697_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(
    mut v_d_698_: *mut leanh::LeanObject,
    mut v_a_699_: u8,
) -> u8 {
    match leanh::lean_obj_tag(v_d_698_) {
        0 => {
            let mut v_val_700_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_701_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_702_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_703_: u8 = 0;
            v_val_700_ = leanh::lean_ctor_get(v_d_698_, 0);
            v_toConstantVal_701_ = leanh::lean_ctor_get(v_val_700_, 0);
            v_type_702_ = leanh::lean_ctor_get(v_toConstantVal_701_, 2);
            v___x_703_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_699_, v_type_702_);
            return v___x_703_;
        }
        4 => {
            return v_a_699_;
        }
        5 => {
            let mut v_defns_704_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_705_: u8 = 0;
            v_defns_704_ = leanh::lean_ctor_get(v_d_698_, 0);
            v___x_705_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_a_699_, v_defns_704_);
            return v___x_705_;
        }
        6 => {
            let mut v_types_706_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_707_: u8 = 0;
            v_types_706_ = leanh::lean_ctor_get(v_d_698_, 2);
            v___x_707_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_a_699_, v_types_706_);
            return v___x_707_;
        }
        _ => {
            let mut v_val_708_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_709_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_710_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_711_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_712_: u8 = 0;
            let mut v___x_713_: u8 = 0;
            v_val_708_ = leanh::lean_ctor_get(v_d_698_, 0);
            v_toConstantVal_709_ = leanh::lean_ctor_get(v_val_708_, 0);
            v_value_710_ = leanh::lean_ctor_get(v_val_708_, 1);
            v_type_711_ = leanh::lean_ctor_get(v_toConstantVal_709_, 2);
            v___x_712_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_699_, v_type_711_);
            v___x_713_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_712_, v_value_710_);
            return v___x_713_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(
    mut v_d_714_: *mut leanh::LeanObject,
    mut v_a_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_716_: u8 = 0;
    let mut v_res_717_: u8 = 0;
    let mut v_r_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_716_ = (leanh::lean_unbox(v_a_715_) as u8);
    v_res_717_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(
        v_d_714_,
        v_a_boxed_716_,
    );
    leanh::lean_dec(v_d_714_);
    v_r_718_ = leanh::lean_box((v_res_717_) as usize);
    return v_r_718_;
}
pub unsafe fn l_Lean_Declaration_hasSyntheticSorry(
    mut v_d_719_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: u8 = 0;
    v___x_720_ = 0;
    v___x_721_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(
        v_d_719_, v___x_720_,
    );
    return v___x_721_;
}
pub unsafe fn l_Lean_Declaration_hasSyntheticSorry___boxed(
    mut v_d_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Lean_Declaration_hasSyntheticSorry(v_d_722_);
    leanh::lean_dec(v_d_722_);
    v_r_724_ = leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(
    mut v_r_725_: u8,
    mut v_e_726_: *mut leanh::LeanObject,
) -> u8 {
    if v_r_725_ == 0 {
        let mut v___x_727_: u8 = 0;
        v___x_727_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_726_);
        return v___x_727_;
    } else {
        return v_r_725_;
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(
    mut v_r_728_: *mut leanh::LeanObject,
    mut v_e_729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_boxed_730_: u8 = 0;
    let mut v_res_731_: u8 = 0;
    let mut v_r_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_730_ = (leanh::lean_unbox(v_r_728_) as u8);
    v_res_731_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_boxed_730_, v_e_729_);
    leanh::lean_dec_ref(v_e_729_);
    v_r_732_ = leanh::lean_box((v_res_731_) as usize);
    return v_r_732_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(
    mut v_x_733_: u8,
    mut v_x_734_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    let mut v___x_741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_734_) == 0 {
                    return v_x_733_;
                } else {
                    v_head_735_ = leanh::lean_ctor_get(v_x_734_, 0);
                    v_toConstantVal_736_ = leanh::lean_ctor_get(v_head_735_, 0);
                    v_tail_737_ = leanh::lean_ctor_get(v_x_734_, 1);
                    v_value_738_ = leanh::lean_ctor_get(v_head_735_, 1);
                    v_type_739_ = leanh::lean_ctor_get(v_toConstantVal_736_, 2);
                    v___x_740_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_x_733_, v_type_739_);
                    v___x_741_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_740_, v_value_738_);
                    v_x_733_ = v___x_741_;
                    v_x_734_ = v_tail_737_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(
    mut v_x_743_: *mut leanh::LeanObject,
    mut v_x_744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1024__boxed_745_: u8 = 0;
    let mut v_res_746_: u8 = 0;
    let mut v_r_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_745_ = (leanh::lean_unbox(v_x_743_) as u8);
    v_res_746_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_745_, v_x_744_);
    leanh::lean_dec(v_x_744_);
    v_r_747_ = leanh::lean_box((v_res_746_) as usize);
    return v_r_747_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(
    mut v_x_748_: u8,
    mut v_x_749_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v_tail_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_749_) == 0 {
                    return v_x_748_;
                } else {
                    if v_x_748_ == 0 {
                        v_head_750_ = leanh::lean_ctor_get(v_x_749_, 0);
                        v_tail_751_ = leanh::lean_ctor_get(v_x_749_, 1);
                        v_type_752_ = leanh::lean_ctor_get(v_head_750_, 1);
                        v___x_753_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_752_);
                        v_x_748_ = v___x_753_;
                        v_x_749_ = v_tail_751_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_755_ = leanh::lean_ctor_get(v_x_749_, 1);
                        v_x_749_ = v_tail_755_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(
    mut v_x_757_: *mut leanh::LeanObject,
    mut v_x_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1040__boxed_759_: u8 = 0;
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_759_ = (leanh::lean_unbox(v_x_757_) as u8);
    v_res_760_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_759_, v_x_758_);
    leanh::lean_dec(v_x_758_);
    v_r_761_ = leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(
    mut v_x_762_: u8,
    mut v_x_763_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_763_) == 0 {
        return v_x_762_;
    } else {
        if v_x_762_ == 0 {
            let mut v_head_764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_767_: u8 = 0;
            let mut v___x_768_: u8 = 0;
            v_head_764_ = leanh::lean_ctor_get(v_x_763_, 0);
            v_tail_765_ = leanh::lean_ctor_get(v_x_763_, 1);
            v_type_766_ = leanh::lean_ctor_get(v_head_764_, 1);
            v___x_767_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_766_);
            v___x_768_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v___x_767_, v_tail_765_);
            return v___x_768_;
        } else {
            let mut v_tail_769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_770_: u8 = 0;
            v_tail_769_ = leanh::lean_ctor_get(v_x_763_, 1);
            v___x_770_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_762_, v_tail_769_);
            return v___x_770_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(
    mut v_x_771_: *mut leanh::LeanObject,
    mut v_x_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1058__boxed_773_: u8 = 0;
    let mut v_res_774_: u8 = 0;
    let mut v_r_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_773_ = (leanh::lean_unbox(v_x_771_) as u8);
    v_res_774_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_773_, v_x_772_);
    leanh::lean_dec(v_x_772_);
    v_r_775_ = leanh::lean_box((v_res_774_) as usize);
    return v_r_775_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(
    mut v_x_776_: u8,
    mut v_x_777_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_783_: u8 = 0;
    let mut v___x_784_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_777_) == 0 {
                    return v_x_776_;
                } else {
                    v_head_778_ = leanh::lean_ctor_get(v_x_777_, 0);
                    v_tail_779_ = leanh::lean_ctor_get(v_x_777_, 1);
                    v_type_780_ = leanh::lean_ctor_get(v_head_778_, 1);
                    v_ctors_781_ = leanh::lean_ctor_get(v_head_778_, 2);
                    if v_x_776_ == 0 {
                        v___x_786_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_780_);
                        v___y_783_ = v___x_786_;
                        state = 1;
                        continue;
                    } else {
                        v___y_783_ = v_x_776_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_784_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_783_, v_ctors_781_);
                v_x_776_ = v___x_784_;
                v_x_777_ = v_tail_779_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(
    mut v_x_787_: *mut leanh::LeanObject,
    mut v_x_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1076__boxed_789_: u8 = 0;
    let mut v_res_790_: u8 = 0;
    let mut v_r_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_789_ = (leanh::lean_unbox(v_x_787_) as u8);
    v_res_790_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_789_, v_x_788_);
    leanh::lean_dec(v_x_788_);
    v_r_791_ = leanh::lean_box((v_res_790_) as usize);
    return v_r_791_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(
    mut v_x_792_: u8,
    mut v_x_793_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_head_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: u8 = 0;
    let mut v___x_800_: u8 = 0;
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_793_) == 0 {
                    return v_x_792_;
                } else {
                    v_head_794_ = leanh::lean_ctor_get(v_x_793_, 0);
                    v_tail_795_ = leanh::lean_ctor_get(v_x_793_, 1);
                    v_type_796_ = leanh::lean_ctor_get(v_head_794_, 1);
                    v_ctors_797_ = leanh::lean_ctor_get(v_head_794_, 2);
                    if v_x_792_ == 0 {
                        v___x_802_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_796_);
                        v___y_799_ = v___x_802_;
                        state = 1;
                        continue;
                    } else {
                        v___y_799_ = v_x_792_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_800_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_799_, v_ctors_797_);
                v___x_801_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v___x_800_, v_tail_795_);
                return v___x_801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(
    mut v_x_803_: *mut leanh::LeanObject,
    mut v_x_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1096__boxed_805_: u8 = 0;
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_805_ = (leanh::lean_unbox(v_x_803_) as u8);
    v_res_806_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_805_, v_x_804_);
    leanh::lean_dec(v_x_804_);
    v_r_807_ = leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(
    mut v_d_808_: *mut leanh::LeanObject,
    mut v_a_809_: u8,
) -> u8 {
    match leanh::lean_obj_tag(v_d_808_) {
        0 => {
            let mut v_val_810_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_811_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_812_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_813_: u8 = 0;
            v_val_810_ = leanh::lean_ctor_get(v_d_808_, 0);
            v_toConstantVal_811_ = leanh::lean_ctor_get(v_val_810_, 0);
            v_type_812_ = leanh::lean_ctor_get(v_toConstantVal_811_, 2);
            v___x_813_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_809_, v_type_812_);
            return v___x_813_;
        }
        4 => {
            return v_a_809_;
        }
        5 => {
            let mut v_defns_814_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_815_: u8 = 0;
            v_defns_814_ = leanh::lean_ctor_get(v_d_808_, 0);
            v___x_815_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_a_809_, v_defns_814_);
            return v___x_815_;
        }
        6 => {
            let mut v_types_816_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_817_: u8 = 0;
            v_types_816_ = leanh::lean_ctor_get(v_d_808_, 2);
            v___x_817_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_a_809_, v_types_816_);
            return v___x_817_;
        }
        _ => {
            let mut v_val_818_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_819_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_820_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_821_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: u8 = 0;
            let mut v___x_823_: u8 = 0;
            v_val_818_ = leanh::lean_ctor_get(v_d_808_, 0);
            v_toConstantVal_819_ = leanh::lean_ctor_get(v_val_818_, 0);
            v_value_820_ = leanh::lean_ctor_get(v_val_818_, 1);
            v_type_821_ = leanh::lean_ctor_get(v_toConstantVal_819_, 2);
            v___x_822_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_809_, v_type_821_);
            v___x_823_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_822_, v_value_820_);
            return v___x_823_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(
    mut v_d_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_826_: u8 = 0;
    let mut v_res_827_: u8 = 0;
    let mut v_r_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_826_ = (leanh::lean_unbox(v_a_825_) as u8);
    v_res_827_ =
        l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(
            v_d_824_,
            v_a_boxed_826_,
        );
    leanh::lean_dec(v_d_824_);
    v_r_828_ = leanh::lean_box((v_res_827_) as usize);
    return v_r_828_;
}
pub unsafe fn l_Lean_Declaration_hasNonSyntheticSorry(
    mut v_d_829_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_830_: u8 = 0;
    let mut v___x_831_: u8 = 0;
    v___x_830_ = 0;
    v___x_831_ =
        l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(
            v_d_829_, v___x_830_,
        );
    return v___x_831_;
}
pub unsafe fn l_Lean_Declaration_hasNonSyntheticSorry___boxed(
    mut v_d_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_833_: u8 = 0;
    let mut v_r_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_833_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_832_);
    leanh::lean_dec(v_d_832_);
    v_r_834_ = leanh::lean_box((v_res_833_) as usize);
    return v_r_834_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Sorry(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Declaration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Sorry(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Sorry(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_FindExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Declaration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Sorry(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Sorry(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Sorry(builtin);
}