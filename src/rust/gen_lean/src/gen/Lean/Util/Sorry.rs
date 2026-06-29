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
pub static l_Lean_Expr_isSorry___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_isSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isSorry___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5207765522374246084 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isSorry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSorry___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isSyntheticSorry___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_isSyntheticSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isSyntheticSorry___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_isSyntheticSorry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_isSyntheticSorry___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__1_value)
                as *mut crate::leanh::LeanObject,
            9255189395584251158 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isSyntheticSorry___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_isNonSyntheticSorry___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Expr_isNonSyntheticSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isSyntheticSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Expr_isNonSyntheticSorry___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15761733860085307253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Expr_isNonSyntheticSorry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_isNonSyntheticSorry___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_hasSorry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_hasSorry___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasSorry___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_hasSyntheticSorry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_isSyntheticSorry___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasSyntheticSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasSyntheticSorry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Expr_hasNonSyntheticSorry___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Expr_isNonSyntheticSorry___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Expr_hasNonSyntheticSorry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_hasNonSyntheticSorry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Expr_isSorry(mut v_e_421_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    v___x_422_ = l_Lean_Expr_isSorry___closed__1;
    v___x_423_ = l_Lean_Expr_isAppOf(v_e_421_, v___x_422_);
    return v___x_423_;
}
pub unsafe fn l_Lean_Expr_isSorry___boxed(
    mut v_e_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_425_: u8 = 0;
    let mut v_r_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_425_ = l_Lean_Expr_isSorry(v_e_424_);
    crate::leanh::lean_dec_ref(v_e_424_);
    v_r_426_ = crate::leanh::lean_box((v_res_425_) as usize);
    return v_r_426_;
}
pub unsafe fn l_Lean_Expr_isSyntheticSorry(mut v_e_432_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_434_: u8 = 0;
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v___x_444_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_445_ = l_Lean_Expr_getAppNumArgs(v_e_432_);
                    v___x_446_ = lean_nat_dec_le(v___x_444_, v___x_445_);
                    crate::leanh::lean_dec(v___x_445_);
                    v___y_434_ = v___x_446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_434_ == 0 {
                    return v___y_434_;
                } else {
                    v___x_435_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_436_ = l_Lean_Expr_getAppNumArgs(v_e_432_);
                    v___x_437_ = lean_nat_sub(v___x_436_, v___x_435_);
                    crate::leanh::lean_dec(v___x_436_);
                    v___x_438_ = lean_nat_sub(v___x_437_, v___x_435_);
                    crate::leanh::lean_dec(v___x_437_);
                    v___x_439_ = l_Lean_Expr_getRevArg_x21(v_e_432_, v___x_438_);
                    v___x_440_ = l_Lean_Expr_isSyntheticSorry___closed__2;
                    v___x_441_ = l_Lean_Expr_isConstOf(v___x_439_, v___x_440_);
                    crate::leanh::lean_dec_ref(v___x_439_);
                    return v___x_441_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_isSyntheticSorry___boxed(
    mut v_e_447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_448_: u8 = 0;
    let mut v_r_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_448_ = l_Lean_Expr_isSyntheticSorry(v_e_447_);
    crate::leanh::lean_dec_ref(v_e_447_);
    v_r_449_ = crate::leanh::lean_box((v_res_448_) as usize);
    return v_r_449_;
}
pub unsafe fn l_Lean_Expr_isNonSyntheticSorry(mut v_e_454_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_456_: u8 = 0;
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v___x_466_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_467_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
                    v___x_468_ = lean_nat_dec_le(v___x_466_, v___x_467_);
                    crate::leanh::lean_dec(v___x_467_);
                    v___y_456_ = v___x_468_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_456_ == 0 {
                    return v___y_456_;
                } else {
                    v___x_457_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_458_ = l_Lean_Expr_getAppNumArgs(v_e_454_);
                    v___x_459_ = lean_nat_sub(v___x_458_, v___x_457_);
                    crate::leanh::lean_dec(v___x_458_);
                    v___x_460_ = lean_nat_sub(v___x_459_, v___x_457_);
                    crate::leanh::lean_dec(v___x_459_);
                    v___x_461_ = l_Lean_Expr_getRevArg_x21(v_e_454_, v___x_460_);
                    v___x_462_ = l_Lean_Expr_isNonSyntheticSorry___closed__1;
                    v___x_463_ = l_Lean_Expr_isConstOf(v___x_461_, v___x_462_);
                    crate::leanh::lean_dec_ref(v___x_461_);
                    return v___x_463_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_isNonSyntheticSorry___boxed(
    mut v_e_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_470_: u8 = 0;
    let mut v_r_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Lean_Expr_isNonSyntheticSorry(v_e_469_);
    crate::leanh::lean_dec_ref(v_e_469_);
    v_r_471_ = crate::leanh::lean_box((v_res_470_) as usize);
    return v_r_471_;
}
pub unsafe fn l_Lean_Expr_hasSorry___lam__0(mut v_x_472_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: u8 = 0;
    v___x_473_ = l_Lean_Expr_isSorry___closed__1;
    v___x_474_ = l_Lean_Expr_isConstOf(v_x_472_, v___x_473_);
    return v___x_474_;
}
pub unsafe fn l_Lean_Expr_hasSorry___lam__0___boxed(
    mut v_x_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_476_: u8 = 0;
    let mut v_r_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Lean_Expr_hasSorry___lam__0(v_x_475_);
    crate::leanh::lean_dec_ref(v_x_475_);
    v_r_477_ = crate::leanh::lean_box((v_res_476_) as usize);
    return v_r_477_;
}
pub unsafe fn l_Lean_Expr_hasSorry(mut v_e_479_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___f_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_480_ = l_Lean_Expr_hasSorry___closed__0;
    v___x_481_ = lean_find_expr(v___f_480_, v_e_479_);
    if crate::leanh::lean_obj_tag(v___x_481_) == 0 {
        let mut v___x_482_: u8 = 0;
        v___x_482_ = 0;
        return v___x_482_;
    } else {
        let mut v___x_483_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_481_, 1);
        v___x_483_ = 1;
        return v___x_483_;
    }
}
pub unsafe fn l_Lean_Expr_hasSorry___boxed(
    mut v_e_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_485_: u8 = 0;
    let mut v_r_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_485_ = l_Lean_Expr_hasSorry(v_e_484_);
    crate::leanh::lean_dec_ref(v_e_484_);
    v_r_486_ = crate::leanh::lean_box((v_res_485_) as usize);
    return v_r_486_;
}
pub unsafe fn l_Lean_Expr_hasSyntheticSorry(mut v_e_488_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___f_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_489_ = l_Lean_Expr_hasSyntheticSorry___closed__0;
    v___x_490_ = lean_find_expr(v___f_489_, v_e_488_);
    if crate::leanh::lean_obj_tag(v___x_490_) == 0 {
        let mut v___x_491_: u8 = 0;
        v___x_491_ = 0;
        return v___x_491_;
    } else {
        let mut v___x_492_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_490_, 1);
        v___x_492_ = 1;
        return v___x_492_;
    }
}
pub unsafe fn l_Lean_Expr_hasSyntheticSorry___boxed(
    mut v_e_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_494_: u8 = 0;
    let mut v_r_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l_Lean_Expr_hasSyntheticSorry(v_e_493_);
    crate::leanh::lean_dec_ref(v_e_493_);
    v_r_495_ = crate::leanh::lean_box((v_res_494_) as usize);
    return v_r_495_;
}
pub unsafe fn l_Lean_Expr_hasNonSyntheticSorry(mut v_e_497_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___f_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_498_ = l_Lean_Expr_hasNonSyntheticSorry___closed__0;
    v___x_499_ = lean_find_expr(v___f_498_, v_e_497_);
    if crate::leanh::lean_obj_tag(v___x_499_) == 0 {
        let mut v___x_500_: u8 = 0;
        v___x_500_ = 0;
        return v___x_500_;
    } else {
        let mut v___x_501_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_499_, 1);
        v___x_501_ = 1;
        return v___x_501_;
    }
}
pub unsafe fn l_Lean_Expr_hasNonSyntheticSorry___boxed(
    mut v_e_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_503_: u8 = 0;
    let mut v_r_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_502_);
    crate::leanh::lean_dec_ref(v_e_502_);
    v_r_504_ = crate::leanh::lean_box((v_res_503_) as usize);
    return v_r_504_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
    mut v_r_505_: u8,
    mut v_e_506_: *mut crate::leanh::LeanObject,
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
    mut v_r_508_: *mut crate::leanh::LeanObject,
    mut v_e_509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_boxed_510_: u8 = 0;
    let mut v_res_511_: u8 = 0;
    let mut v_r_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_510_ = (crate::leanh::lean_unbox(v_r_508_) as u8);
    v_res_511_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(
        v_r_boxed_510_,
        v_e_509_,
    );
    crate::leanh::lean_dec_ref(v_e_509_);
    v_r_512_ = crate::leanh::lean_box((v_res_511_) as usize);
    return v_r_512_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(
    mut v_x_513_: u8,
    mut v_x_514_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: u8 = 0;
    let mut v___x_521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_514_) == 0 {
                    return v_x_513_;
                } else {
                    v_head_515_ = crate::leanh::lean_ctor_get(v_x_514_, 0);
                    v_toConstantVal_516_ = crate::leanh::lean_ctor_get(v_head_515_, 0);
                    v_tail_517_ = crate::leanh::lean_ctor_get(v_x_514_, 1);
                    v_value_518_ = crate::leanh::lean_ctor_get(v_head_515_, 1);
                    v_type_519_ = crate::leanh::lean_ctor_get(v_toConstantVal_516_, 2);
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
    mut v_x_523_: *mut crate::leanh::LeanObject,
    mut v_x_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1024__boxed_525_: u8 = 0;
    let mut v_res_526_: u8 = 0;
    let mut v_r_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_525_ = (crate::leanh::lean_unbox(v_x_523_) as u8);
    v_res_526_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_1024__boxed_525_, v_x_524_);
    crate::leanh::lean_dec(v_x_524_);
    v_r_527_ = crate::leanh::lean_box((v_res_526_) as usize);
    return v_r_527_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(
    mut v_x_528_: u8,
    mut v_x_529_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v_tail_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_529_) == 0 {
                    return v_x_528_;
                } else {
                    if v_x_528_ == 0 {
                        v_head_530_ = crate::leanh::lean_ctor_get(v_x_529_, 0);
                        v_tail_531_ = crate::leanh::lean_ctor_get(v_x_529_, 1);
                        v_type_532_ = crate::leanh::lean_ctor_get(v_head_530_, 1);
                        v___x_533_ = l_Lean_Expr_hasSorry(v_type_532_);
                        v_x_528_ = v___x_533_;
                        v_x_529_ = v_tail_531_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_535_ = crate::leanh::lean_ctor_get(v_x_529_, 1);
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
    mut v_x_537_: *mut crate::leanh::LeanObject,
    mut v_x_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1040__boxed_539_: u8 = 0;
    let mut v_res_540_: u8 = 0;
    let mut v_r_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_539_ = (crate::leanh::lean_unbox(v_x_537_) as u8);
    v_res_540_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_539_, v_x_538_);
    crate::leanh::lean_dec(v_x_538_);
    v_r_541_ = crate::leanh::lean_box((v_res_540_) as usize);
    return v_r_541_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(
    mut v_x_542_: u8,
    mut v_x_543_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_543_) == 0 {
        return v_x_542_;
    } else {
        if v_x_542_ == 0 {
            let mut v_head_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_547_: u8 = 0;
            let mut v___x_548_: u8 = 0;
            v_head_544_ = crate::leanh::lean_ctor_get(v_x_543_, 0);
            v_tail_545_ = crate::leanh::lean_ctor_get(v_x_543_, 1);
            v_type_546_ = crate::leanh::lean_ctor_get(v_head_544_, 1);
            v___x_547_ = l_Lean_Expr_hasSorry(v_type_546_);
            v___x_548_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v___x_547_, v_tail_545_);
            return v___x_548_;
        } else {
            let mut v_tail_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_550_: u8 = 0;
            v_tail_549_ = crate::leanh::lean_ctor_get(v_x_543_, 1);
            v___x_550_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_542_, v_tail_549_);
            return v___x_550_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(
    mut v_x_551_: *mut crate::leanh::LeanObject,
    mut v_x_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1058__boxed_553_: u8 = 0;
    let mut v_res_554_: u8 = 0;
    let mut v_r_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_553_ = (crate::leanh::lean_unbox(v_x_551_) as u8);
    v_res_554_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_1058__boxed_553_, v_x_552_);
    crate::leanh::lean_dec(v_x_552_);
    v_r_555_ = crate::leanh::lean_box((v_res_554_) as usize);
    return v_r_555_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(
    mut v_x_556_: u8,
    mut v_x_557_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_563_: u8 = 0;
    let mut v___x_564_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_557_) == 0 {
                    return v_x_556_;
                } else {
                    v_head_558_ = crate::leanh::lean_ctor_get(v_x_557_, 0);
                    v_tail_559_ = crate::leanh::lean_ctor_get(v_x_557_, 1);
                    v_type_560_ = crate::leanh::lean_ctor_get(v_head_558_, 1);
                    v_ctors_561_ = crate::leanh::lean_ctor_get(v_head_558_, 2);
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
    mut v_x_567_: *mut crate::leanh::LeanObject,
    mut v_x_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1076__boxed_569_: u8 = 0;
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_569_ = (crate::leanh::lean_unbox(v_x_567_) as u8);
    v_res_570_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_569_, v_x_568_);
    crate::leanh::lean_dec(v_x_568_);
    v_r_571_ = crate::leanh::lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(
    mut v_x_572_: u8,
    mut v_x_573_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_579_: u8 = 0;
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_573_) == 0 {
                    return v_x_572_;
                } else {
                    v_head_574_ = crate::leanh::lean_ctor_get(v_x_573_, 0);
                    v_tail_575_ = crate::leanh::lean_ctor_get(v_x_573_, 1);
                    v_type_576_ = crate::leanh::lean_ctor_get(v_head_574_, 1);
                    v_ctors_577_ = crate::leanh::lean_ctor_get(v_head_574_, 2);
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
    mut v_x_583_: *mut crate::leanh::LeanObject,
    mut v_x_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1096__boxed_585_: u8 = 0;
    let mut v_res_586_: u8 = 0;
    let mut v_r_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_585_ = (crate::leanh::lean_unbox(v_x_583_) as u8);
    v_res_586_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_1096__boxed_585_, v_x_584_);
    crate::leanh::lean_dec(v_x_584_);
    v_r_587_ = crate::leanh::lean_box((v_res_586_) as usize);
    return v_r_587_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
    mut v_d_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: u8,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_d_588_) {
        0 => {
            let mut v_val_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_593_: u8 = 0;
            v_val_590_ = crate::leanh::lean_ctor_get(v_d_588_, 0);
            v_toConstantVal_591_ = crate::leanh::lean_ctor_get(v_val_590_, 0);
            v_type_592_ = crate::leanh::lean_ctor_get(v_toConstantVal_591_, 2);
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
            let mut v_defns_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_595_: u8 = 0;
            v_defns_594_ = crate::leanh::lean_ctor_get(v_d_588_, 0);
            v___x_595_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_a_589_, v_defns_594_);
            return v___x_595_;
        }
        6 => {
            let mut v_types_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_597_: u8 = 0;
            v_types_596_ = crate::leanh::lean_ctor_get(v_d_588_, 2);
            v___x_597_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_a_589_, v_types_596_);
            return v___x_597_;
        }
        _ => {
            let mut v_val_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_602_: u8 = 0;
            let mut v___x_603_: u8 = 0;
            v_val_598_ = crate::leanh::lean_ctor_get(v_d_588_, 0);
            v_toConstantVal_599_ = crate::leanh::lean_ctor_get(v_val_598_, 0);
            v_value_600_ = crate::leanh::lean_ctor_get(v_val_598_, 1);
            v_type_601_ = crate::leanh::lean_ctor_get(v_toConstantVal_599_, 2);
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
    mut v_d_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_606_: u8 = 0;
    let mut v_res_607_: u8 = 0;
    let mut v_r_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_606_ = (crate::leanh::lean_unbox(v_a_605_) as u8);
    v_res_607_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
        v_d_604_,
        v_a_boxed_606_,
    );
    crate::leanh::lean_dec(v_d_604_);
    v_r_608_ = crate::leanh::lean_box((v_res_607_) as usize);
    return v_r_608_;
}
pub unsafe fn l_Lean_Declaration_hasSorry(mut v_d_609_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_610_: u8 = 0;
    let mut v___x_611_: u8 = 0;
    v___x_610_ = 0;
    v___x_611_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(
        v_d_609_, v___x_610_,
    );
    return v___x_611_;
}
pub unsafe fn l_Lean_Declaration_hasSorry___boxed(
    mut v_d_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_613_: u8 = 0;
    let mut v_r_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_613_ = l_Lean_Declaration_hasSorry(v_d_612_);
    crate::leanh::lean_dec(v_d_612_);
    v_r_614_ = crate::leanh::lean_box((v_res_613_) as usize);
    return v_r_614_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(
    mut v_r_615_: u8,
    mut v_e_616_: *mut crate::leanh::LeanObject,
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
    mut v_r_618_: *mut crate::leanh::LeanObject,
    mut v_e_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_boxed_620_: u8 = 0;
    let mut v_res_621_: u8 = 0;
    let mut v_r_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_620_ = (crate::leanh::lean_unbox(v_r_618_) as u8);
    v_res_621_ =
        l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(
            v_r_boxed_620_,
            v_e_619_,
        );
    crate::leanh::lean_dec_ref(v_e_619_);
    v_r_622_ = crate::leanh::lean_box((v_res_621_) as usize);
    return v_r_622_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(
    mut v_x_623_: u8,
    mut v_x_624_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_624_) == 0 {
                    return v_x_623_;
                } else {
                    v_head_625_ = crate::leanh::lean_ctor_get(v_x_624_, 0);
                    v_toConstantVal_626_ = crate::leanh::lean_ctor_get(v_head_625_, 0);
                    v_tail_627_ = crate::leanh::lean_ctor_get(v_x_624_, 1);
                    v_value_628_ = crate::leanh::lean_ctor_get(v_head_625_, 1);
                    v_type_629_ = crate::leanh::lean_ctor_get(v_toConstantVal_626_, 2);
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
    mut v_x_633_: *mut crate::leanh::LeanObject,
    mut v_x_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1024__boxed_635_: u8 = 0;
    let mut v_res_636_: u8 = 0;
    let mut v_r_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_635_ = (crate::leanh::lean_unbox(v_x_633_) as u8);
    v_res_636_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_635_, v_x_634_);
    crate::leanh::lean_dec(v_x_634_);
    v_r_637_ = crate::leanh::lean_box((v_res_636_) as usize);
    return v_r_637_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(
    mut v_x_638_: u8,
    mut v_x_639_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut v_tail_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_639_) == 0 {
                    return v_x_638_;
                } else {
                    if v_x_638_ == 0 {
                        v_head_640_ = crate::leanh::lean_ctor_get(v_x_639_, 0);
                        v_tail_641_ = crate::leanh::lean_ctor_get(v_x_639_, 1);
                        v_type_642_ = crate::leanh::lean_ctor_get(v_head_640_, 1);
                        v___x_643_ = l_Lean_Expr_hasSyntheticSorry(v_type_642_);
                        v_x_638_ = v___x_643_;
                        v_x_639_ = v_tail_641_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_645_ = crate::leanh::lean_ctor_get(v_x_639_, 1);
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
    mut v_x_647_: *mut crate::leanh::LeanObject,
    mut v_x_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1040__boxed_649_: u8 = 0;
    let mut v_res_650_: u8 = 0;
    let mut v_r_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_649_ = (crate::leanh::lean_unbox(v_x_647_) as u8);
    v_res_650_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_649_, v_x_648_);
    crate::leanh::lean_dec(v_x_648_);
    v_r_651_ = crate::leanh::lean_box((v_res_650_) as usize);
    return v_r_651_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(
    mut v_x_652_: u8,
    mut v_x_653_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_653_) == 0 {
        return v_x_652_;
    } else {
        if v_x_652_ == 0 {
            let mut v_head_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_657_: u8 = 0;
            let mut v___x_658_: u8 = 0;
            v_head_654_ = crate::leanh::lean_ctor_get(v_x_653_, 0);
            v_tail_655_ = crate::leanh::lean_ctor_get(v_x_653_, 1);
            v_type_656_ = crate::leanh::lean_ctor_get(v_head_654_, 1);
            v___x_657_ = l_Lean_Expr_hasSyntheticSorry(v_type_656_);
            v___x_658_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v___x_657_, v_tail_655_);
            return v___x_658_;
        } else {
            let mut v_tail_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_660_: u8 = 0;
            v_tail_659_ = crate::leanh::lean_ctor_get(v_x_653_, 1);
            v___x_660_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_652_, v_tail_659_);
            return v___x_660_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(
    mut v_x_661_: *mut crate::leanh::LeanObject,
    mut v_x_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1058__boxed_663_: u8 = 0;
    let mut v_res_664_: u8 = 0;
    let mut v_r_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_663_ = (crate::leanh::lean_unbox(v_x_661_) as u8);
    v_res_664_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_663_, v_x_662_);
    crate::leanh::lean_dec(v_x_662_);
    v_r_665_ = crate::leanh::lean_box((v_res_664_) as usize);
    return v_r_665_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(
    mut v_x_666_: u8,
    mut v_x_667_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_673_: u8 = 0;
    let mut v___x_674_: u8 = 0;
    let mut v___x_676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_667_) == 0 {
                    return v_x_666_;
                } else {
                    v_head_668_ = crate::leanh::lean_ctor_get(v_x_667_, 0);
                    v_tail_669_ = crate::leanh::lean_ctor_get(v_x_667_, 1);
                    v_type_670_ = crate::leanh::lean_ctor_get(v_head_668_, 1);
                    v_ctors_671_ = crate::leanh::lean_ctor_get(v_head_668_, 2);
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
    mut v_x_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1076__boxed_679_: u8 = 0;
    let mut v_res_680_: u8 = 0;
    let mut v_r_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_679_ = (crate::leanh::lean_unbox(v_x_677_) as u8);
    v_res_680_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_679_, v_x_678_);
    crate::leanh::lean_dec(v_x_678_);
    v_r_681_ = crate::leanh::lean_box((v_res_680_) as usize);
    return v_r_681_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(
    mut v_x_682_: u8,
    mut v_x_683_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_689_: u8 = 0;
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_683_) == 0 {
                    return v_x_682_;
                } else {
                    v_head_684_ = crate::leanh::lean_ctor_get(v_x_683_, 0);
                    v_tail_685_ = crate::leanh::lean_ctor_get(v_x_683_, 1);
                    v_type_686_ = crate::leanh::lean_ctor_get(v_head_684_, 1);
                    v_ctors_687_ = crate::leanh::lean_ctor_get(v_head_684_, 2);
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
    mut v_x_693_: *mut crate::leanh::LeanObject,
    mut v_x_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1096__boxed_695_: u8 = 0;
    let mut v_res_696_: u8 = 0;
    let mut v_r_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_695_ = (crate::leanh::lean_unbox(v_x_693_) as u8);
    v_res_696_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_695_, v_x_694_);
    crate::leanh::lean_dec(v_x_694_);
    v_r_697_ = crate::leanh::lean_box((v_res_696_) as usize);
    return v_r_697_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(
    mut v_d_698_: *mut crate::leanh::LeanObject,
    mut v_a_699_: u8,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_d_698_) {
        0 => {
            let mut v_val_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_703_: u8 = 0;
            v_val_700_ = crate::leanh::lean_ctor_get(v_d_698_, 0);
            v_toConstantVal_701_ = crate::leanh::lean_ctor_get(v_val_700_, 0);
            v_type_702_ = crate::leanh::lean_ctor_get(v_toConstantVal_701_, 2);
            v___x_703_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_699_, v_type_702_);
            return v___x_703_;
        }
        4 => {
            return v_a_699_;
        }
        5 => {
            let mut v_defns_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_705_: u8 = 0;
            v_defns_704_ = crate::leanh::lean_ctor_get(v_d_698_, 0);
            v___x_705_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_a_699_, v_defns_704_);
            return v___x_705_;
        }
        6 => {
            let mut v_types_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_707_: u8 = 0;
            v_types_706_ = crate::leanh::lean_ctor_get(v_d_698_, 2);
            v___x_707_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_a_699_, v_types_706_);
            return v___x_707_;
        }
        _ => {
            let mut v_val_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_712_: u8 = 0;
            let mut v___x_713_: u8 = 0;
            v_val_708_ = crate::leanh::lean_ctor_get(v_d_698_, 0);
            v_toConstantVal_709_ = crate::leanh::lean_ctor_get(v_val_708_, 0);
            v_value_710_ = crate::leanh::lean_ctor_get(v_val_708_, 1);
            v_type_711_ = crate::leanh::lean_ctor_get(v_toConstantVal_709_, 2);
            v___x_712_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_699_, v_type_711_);
            v___x_713_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_712_, v_value_710_);
            return v___x_713_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(
    mut v_d_714_: *mut crate::leanh::LeanObject,
    mut v_a_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_716_: u8 = 0;
    let mut v_res_717_: u8 = 0;
    let mut v_r_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_716_ = (crate::leanh::lean_unbox(v_a_715_) as u8);
    v_res_717_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(
        v_d_714_,
        v_a_boxed_716_,
    );
    crate::leanh::lean_dec(v_d_714_);
    v_r_718_ = crate::leanh::lean_box((v_res_717_) as usize);
    return v_r_718_;
}
pub unsafe fn l_Lean_Declaration_hasSyntheticSorry(
    mut v_d_719_: *mut crate::leanh::LeanObject,
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
    mut v_d_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_723_: u8 = 0;
    let mut v_r_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_723_ = l_Lean_Declaration_hasSyntheticSorry(v_d_722_);
    crate::leanh::lean_dec(v_d_722_);
    v_r_724_ = crate::leanh::lean_box((v_res_723_) as usize);
    return v_r_724_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(
    mut v_r_725_: u8,
    mut v_e_726_: *mut crate::leanh::LeanObject,
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
    mut v_r_728_: *mut crate::leanh::LeanObject,
    mut v_e_729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_boxed_730_: u8 = 0;
    let mut v_res_731_: u8 = 0;
    let mut v_r_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_boxed_730_ = (crate::leanh::lean_unbox(v_r_728_) as u8);
    v_res_731_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_boxed_730_, v_e_729_);
    crate::leanh::lean_dec_ref(v_e_729_);
    v_r_732_ = crate::leanh::lean_box((v_res_731_) as usize);
    return v_r_732_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(
    mut v_x_733_: u8,
    mut v_x_734_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    let mut v___x_741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_734_) == 0 {
                    return v_x_733_;
                } else {
                    v_head_735_ = crate::leanh::lean_ctor_get(v_x_734_, 0);
                    v_toConstantVal_736_ = crate::leanh::lean_ctor_get(v_head_735_, 0);
                    v_tail_737_ = crate::leanh::lean_ctor_get(v_x_734_, 1);
                    v_value_738_ = crate::leanh::lean_ctor_get(v_head_735_, 1);
                    v_type_739_ = crate::leanh::lean_ctor_get(v_toConstantVal_736_, 2);
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
    mut v_x_743_: *mut crate::leanh::LeanObject,
    mut v_x_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1024__boxed_745_: u8 = 0;
    let mut v_res_746_: u8 = 0;
    let mut v_r_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1024__boxed_745_ = (crate::leanh::lean_unbox(v_x_743_) as u8);
    v_res_746_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_745_, v_x_744_);
    crate::leanh::lean_dec(v_x_744_);
    v_r_747_ = crate::leanh::lean_box((v_res_746_) as usize);
    return v_r_747_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(
    mut v_x_748_: u8,
    mut v_x_749_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v_tail_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_749_) == 0 {
                    return v_x_748_;
                } else {
                    if v_x_748_ == 0 {
                        v_head_750_ = crate::leanh::lean_ctor_get(v_x_749_, 0);
                        v_tail_751_ = crate::leanh::lean_ctor_get(v_x_749_, 1);
                        v_type_752_ = crate::leanh::lean_ctor_get(v_head_750_, 1);
                        v___x_753_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_752_);
                        v_x_748_ = v___x_753_;
                        v_x_749_ = v_tail_751_;
                        state = 0;
                        continue;
                    } else {
                        v_tail_755_ = crate::leanh::lean_ctor_get(v_x_749_, 1);
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
    mut v_x_757_: *mut crate::leanh::LeanObject,
    mut v_x_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1040__boxed_759_: u8 = 0;
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1040__boxed_759_ = (crate::leanh::lean_unbox(v_x_757_) as u8);
    v_res_760_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_759_, v_x_758_);
    crate::leanh::lean_dec(v_x_758_);
    v_r_761_ = crate::leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(
    mut v_x_762_: u8,
    mut v_x_763_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_763_) == 0 {
        return v_x_762_;
    } else {
        if v_x_762_ == 0 {
            let mut v_head_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_767_: u8 = 0;
            let mut v___x_768_: u8 = 0;
            v_head_764_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
            v_tail_765_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
            v_type_766_ = crate::leanh::lean_ctor_get(v_head_764_, 1);
            v___x_767_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_766_);
            v___x_768_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v___x_767_, v_tail_765_);
            return v___x_768_;
        } else {
            let mut v_tail_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_770_: u8 = 0;
            v_tail_769_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
            v___x_770_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_762_, v_tail_769_);
            return v___x_770_;
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(
    mut v_x_771_: *mut crate::leanh::LeanObject,
    mut v_x_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1058__boxed_773_: u8 = 0;
    let mut v_res_774_: u8 = 0;
    let mut v_r_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1058__boxed_773_ = (crate::leanh::lean_unbox(v_x_771_) as u8);
    v_res_774_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_773_, v_x_772_);
    crate::leanh::lean_dec(v_x_772_);
    v_r_775_ = crate::leanh::lean_box((v_res_774_) as usize);
    return v_r_775_;
}
pub unsafe fn l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(
    mut v_x_776_: u8,
    mut v_x_777_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_783_: u8 = 0;
    let mut v___x_784_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_777_) == 0 {
                    return v_x_776_;
                } else {
                    v_head_778_ = crate::leanh::lean_ctor_get(v_x_777_, 0);
                    v_tail_779_ = crate::leanh::lean_ctor_get(v_x_777_, 1);
                    v_type_780_ = crate::leanh::lean_ctor_get(v_head_778_, 1);
                    v_ctors_781_ = crate::leanh::lean_ctor_get(v_head_778_, 2);
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
    mut v_x_787_: *mut crate::leanh::LeanObject,
    mut v_x_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1076__boxed_789_: u8 = 0;
    let mut v_res_790_: u8 = 0;
    let mut v_r_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_789_ = (crate::leanh::lean_unbox(v_x_787_) as u8);
    v_res_790_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_789_, v_x_788_);
    crate::leanh::lean_dec(v_x_788_);
    v_r_791_ = crate::leanh::lean_box((v_res_790_) as usize);
    return v_r_791_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(
    mut v_x_792_: u8,
    mut v_x_793_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_head_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_799_: u8 = 0;
    let mut v___x_800_: u8 = 0;
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_793_) == 0 {
                    return v_x_792_;
                } else {
                    v_head_794_ = crate::leanh::lean_ctor_get(v_x_793_, 0);
                    v_tail_795_ = crate::leanh::lean_ctor_get(v_x_793_, 1);
                    v_type_796_ = crate::leanh::lean_ctor_get(v_head_794_, 1);
                    v_ctors_797_ = crate::leanh::lean_ctor_get(v_head_794_, 2);
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
    mut v_x_803_: *mut crate::leanh::LeanObject,
    mut v_x_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1096__boxed_805_: u8 = 0;
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1096__boxed_805_ = (crate::leanh::lean_unbox(v_x_803_) as u8);
    v_res_806_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_805_, v_x_804_);
    crate::leanh::lean_dec(v_x_804_);
    v_r_807_ = crate::leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(
    mut v_d_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: u8,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_d_808_) {
        0 => {
            let mut v_val_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_813_: u8 = 0;
            v_val_810_ = crate::leanh::lean_ctor_get(v_d_808_, 0);
            v_toConstantVal_811_ = crate::leanh::lean_ctor_get(v_val_810_, 0);
            v_type_812_ = crate::leanh::lean_ctor_get(v_toConstantVal_811_, 2);
            v___x_813_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_809_, v_type_812_);
            return v___x_813_;
        }
        4 => {
            return v_a_809_;
        }
        5 => {
            let mut v_defns_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_815_: u8 = 0;
            v_defns_814_ = crate::leanh::lean_ctor_get(v_d_808_, 0);
            v___x_815_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_a_809_, v_defns_814_);
            return v___x_815_;
        }
        6 => {
            let mut v_types_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_817_: u8 = 0;
            v_types_816_ = crate::leanh::lean_ctor_get(v_d_808_, 2);
            v___x_817_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_a_809_, v_types_816_);
            return v___x_817_;
        }
        _ => {
            let mut v_val_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toConstantVal_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_value_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: u8 = 0;
            let mut v___x_823_: u8 = 0;
            v_val_818_ = crate::leanh::lean_ctor_get(v_d_808_, 0);
            v_toConstantVal_819_ = crate::leanh::lean_ctor_get(v_val_818_, 0);
            v_value_820_ = crate::leanh::lean_ctor_get(v_val_818_, 1);
            v_type_821_ = crate::leanh::lean_ctor_get(v_toConstantVal_819_, 2);
            v___x_822_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_809_, v_type_821_);
            v___x_823_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_822_, v_value_820_);
            return v___x_823_;
        }
    }
}
pub unsafe fn l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(
    mut v_d_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_826_: u8 = 0;
    let mut v_res_827_: u8 = 0;
    let mut v_r_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_826_ = (crate::leanh::lean_unbox(v_a_825_) as u8);
    v_res_827_ =
        l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(
            v_d_824_,
            v_a_boxed_826_,
        );
    crate::leanh::lean_dec(v_d_824_);
    v_r_828_ = crate::leanh::lean_box((v_res_827_) as usize);
    return v_r_828_;
}
pub unsafe fn l_Lean_Declaration_hasNonSyntheticSorry(
    mut v_d_829_: *mut crate::leanh::LeanObject,
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
    mut v_d_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_833_: u8 = 0;
    let mut v_r_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_833_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_832_);
    crate::leanh::lean_dec(v_d_832_);
    v_r_834_ = crate::leanh::lean_box((v_res_833_) as usize);
    return v_r_834_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_FindExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_FindExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Declaration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Sorry(builtin);
}
