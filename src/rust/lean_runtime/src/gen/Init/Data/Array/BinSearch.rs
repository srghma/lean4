// Lean compiler output
// Module: Init.Data.Array.BinSearch
// Imports: Init.Data.Array.Basic Init.Data.Bool Init.Omega Init.WFTactics
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_isSome___boxed;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Array_binSearch___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Array_binSearch___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binSearch___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_binSearchContains___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
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
static mut l_Array_binSearchContains___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binSearchContains___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_binInsert___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Array_binInsert___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_binInsert___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_binInsert___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_binInsert___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Array_binInsert___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_binInsert___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Array_binSearchAux___redArg(
    mut v_lt_427_: *mut LeanObject,
    mut v_found_428_: *mut LeanObject,
    mut v_as_429_: *mut LeanObject,
    mut v_k_430_: *mut LeanObject,
    mut v_x_431_: *mut LeanObject,
    mut v_x_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_447_: u8 = 0;
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_436_ = lean_nat_add(v_x_431_, v_x_432_);
                v___x_437_ = lean_unsigned_to_nat(1);
                v_m_438_ = lean_nat_shiftr(v___x_436_, v___x_437_);
                lean_dec(v___x_436_);
                v_a_439_ = lean_array_fget_borrowed(v_as_429_, v_m_438_);
                lean_inc_ref(v_lt_427_);
                lean_inc(v_k_430_);
                lean_inc(v_a_439_);
                v___x_440_ = lean_apply_2(v_lt_427_, v_a_439_, v_k_430_);
                v___x_441_ = (lean_unbox(v___x_440_) as u8);
                if v___x_441_ == 0 {
                    lean_dec(v_x_432_);
                    lean_inc_ref(v_lt_427_);
                    lean_inc(v_a_439_);
                    lean_inc(v_k_430_);
                    v___x_442_ = lean_apply_2(v_lt_427_, v_k_430_, v_a_439_);
                    v___x_443_ = (lean_unbox(v___x_442_) as u8);
                    if v___x_443_ == 0 {
                        lean_dec(v_m_438_);
                        lean_dec(v_x_431_);
                        lean_dec(v_k_430_);
                        lean_dec_ref(v_lt_427_);
                        lean_inc(v_a_439_);
                        v___x_444_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_444_, 0, v_a_439_);
                        v___x_445_ = lean_apply_1(v_found_428_, v___x_444_);
                        return v___x_445_;
                    } else {
                        v___x_446_ = lean_unsigned_to_nat(0);
                        v___x_447_ = lean_nat_dec_eq(v_m_438_, v___x_446_);
                        if v___x_447_ == 0 {
                            v___x_448_ = lean_nat_sub(v_m_438_, v___x_437_);
                            lean_dec(v_m_438_);
                            v___x_449_ = lean_nat_dec_lt(v___x_448_, v_x_431_);
                            if v___x_449_ == 0 {
                                v_x_432_ = v___x_448_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_448_);
                                lean_dec(v_x_431_);
                                lean_dec(v_k_430_);
                                lean_dec_ref(v_lt_427_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_m_438_);
                            lean_dec(v_x_431_);
                            lean_dec(v_k_430_);
                            lean_dec_ref(v_lt_427_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_x_431_);
                    v___x_451_ = lean_nat_add(v_m_438_, v___x_437_);
                    lean_dec(v_m_438_);
                    v___x_452_ = lean_nat_dec_le(v___x_451_, v_x_432_);
                    if v___x_452_ == 0 {
                        lean_dec(v___x_451_);
                        lean_dec(v_x_432_);
                        lean_dec(v_k_430_);
                        lean_dec_ref(v_lt_427_);
                        v___x_453_ = lean_box(0);
                        v___x_454_ = lean_apply_1(v_found_428_, v___x_453_);
                        return v___x_454_;
                    } else {
                        v_x_431_ = v___x_451_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_434_ = lean_box(0);
                v___x_435_ = lean_apply_1(v_found_428_, v___x_434_);
                return v___x_435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___redArg___boxed(
    mut v_lt_456_: *mut LeanObject,
    mut v_found_457_: *mut LeanObject,
    mut v_as_458_: *mut LeanObject,
    mut v_k_459_: *mut LeanObject,
    mut v_x_460_: *mut LeanObject,
    mut v_x_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_res_462_ = l_Array_binSearchAux___redArg(
        v_lt_456_,
        v_found_457_,
        v_as_458_,
        v_k_459_,
        v_x_460_,
        v_x_461_,
    );
    lean_dec_ref(v_as_458_);
    return v_res_462_;
}
pub unsafe fn l_Array_binSearchAux(
    mut v_00_u03b1_463_: *mut LeanObject,
    mut v_00_u03b2_464_: *mut LeanObject,
    mut v_lt_465_: *mut LeanObject,
    mut v_found_466_: *mut LeanObject,
    mut v_as_467_: *mut LeanObject,
    mut v_k_468_: *mut LeanObject,
    mut v_x_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
    mut v_x_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    v___x_472_ = l_Array_binSearchAux___redArg(
        v_lt_465_,
        v_found_466_,
        v_as_467_,
        v_k_468_,
        v_x_469_,
        v_x_470_,
    );
    return v___x_472_;
}
pub unsafe fn l_Array_binSearchAux___boxed(
    mut v_00_u03b1_473_: *mut LeanObject,
    mut v_00_u03b2_474_: *mut LeanObject,
    mut v_lt_475_: *mut LeanObject,
    mut v_found_476_: *mut LeanObject,
    mut v_as_477_: *mut LeanObject,
    mut v_k_478_: *mut LeanObject,
    mut v_x_479_: *mut LeanObject,
    mut v_x_480_: *mut LeanObject,
    mut v_x_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_482_: *mut LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Array_binSearchAux(
        v_00_u03b1_473_,
        v_00_u03b2_474_,
        v_lt_475_,
        v_found_476_,
        v_as_477_,
        v_k_478_,
        v_x_479_,
        v_x_480_,
        v_x_481_,
    );
    lean_dec_ref(v_as_477_);
    return v_res_482_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___redArg(
    mut v_x_483_: *mut LeanObject,
    mut v_x_484_: *mut LeanObject,
    mut v_h__1_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_486_ = lean_apply_3(v_h__1_485_, v_x_483_, v_x_484_, lean_box(0));
    return v___x_486_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter(
    mut v_00_u03b1_487_: *mut LeanObject,
    mut v_as_488_: *mut LeanObject,
    mut v_motive_489_: *mut LeanObject,
    mut v_x_490_: *mut LeanObject,
    mut v_x_491_: *mut LeanObject,
    mut v_x_492_: *mut LeanObject,
    mut v_h__1_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = lean_apply_3(v_h__1_493_, v_x_490_, v_x_491_, lean_box(0));
    return v___x_494_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter___boxed(
    mut v_00_u03b1_495_: *mut LeanObject,
    mut v_as_496_: *mut LeanObject,
    mut v_motive_497_: *mut LeanObject,
    mut v_x_498_: *mut LeanObject,
    mut v_x_499_: *mut LeanObject,
    mut v_x_500_: *mut LeanObject,
    mut v_h__1_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_res_502_ = l___private_Init_Data_Array_BinSearch_0__Array_binSearchAux_match__1_splitter(
        v_00_u03b1_495_,
        v_as_496_,
        v_motive_497_,
        v_x_498_,
        v_x_499_,
        v_x_500_,
        v_h__1_501_,
    );
    lean_dec_ref(v_as_496_);
    return v_res_502_;
}
pub unsafe fn l_Array_binSearch___redArg(
    mut v_as_504_: *mut LeanObject,
    mut v_k_505_: *mut LeanObject,
    mut v_lt_506_: *mut LeanObject,
    mut v_lo_507_: *mut LeanObject,
    mut v_hi_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: u8 = 0;
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: u8 = 0;
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_515_ = lean_array_get_size(v_as_504_);
                v___x_516_ = lean_nat_dec_lt(v_lo_507_, v___x_515_);
                if v___x_516_ == 0 {
                    lean_dec(v_hi_508_);
                    lean_dec(v_lo_507_);
                    lean_dec_ref(v_lt_506_);
                    lean_dec(v_k_505_);
                    v___x_517_ = lean_box(0);
                    return v___x_517_;
                } else {
                    v___x_518_ = lean_nat_dec_lt(v_hi_508_, v___x_515_);
                    if v___x_518_ == 0 {
                        lean_dec(v_hi_508_);
                        v___x_519_ = lean_unsigned_to_nat(1);
                        v___x_520_ = lean_nat_sub(v___x_515_, v___x_519_);
                        v___y_510_ = v___x_520_;
                        state = 1;
                        continue;
                    } else {
                        v___y_510_ = v_hi_508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_511_ = lean_nat_dec_le(v_lo_507_, v___y_510_);
                if v___x_511_ == 0 {
                    lean_dec(v___y_510_);
                    lean_dec(v_lo_507_);
                    lean_dec_ref(v_lt_506_);
                    lean_dec(v_k_505_);
                    v___x_512_ = lean_box(0);
                    return v___x_512_;
                } else {
                    v___x_513_ = l_Array_binSearch___redArg___closed__0;
                    v___x_514_ = l_Array_binSearchAux___redArg(
                        v_lt_506_, v___x_513_, v_as_504_, v_k_505_, v_lo_507_, v___y_510_,
                    );
                    return v___x_514_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearch___redArg___boxed(
    mut v_as_521_: *mut LeanObject,
    mut v_k_522_: *mut LeanObject,
    mut v_lt_523_: *mut LeanObject,
    mut v_lo_524_: *mut LeanObject,
    mut v_hi_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Array_binSearch___redArg(v_as_521_, v_k_522_, v_lt_523_, v_lo_524_, v_hi_525_);
    lean_dec_ref(v_as_521_);
    return v_res_526_;
}
pub unsafe fn l_Array_binSearch(
    mut v_00_u03b1_527_: *mut LeanObject,
    mut v_as_528_: *mut LeanObject,
    mut v_k_529_: *mut LeanObject,
    mut v_lt_530_: *mut LeanObject,
    mut v_lo_531_: *mut LeanObject,
    mut v_hi_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: u8 = 0;
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_539_ = lean_array_get_size(v_as_528_);
                v___x_540_ = lean_nat_dec_lt(v_lo_531_, v___x_539_);
                if v___x_540_ == 0 {
                    lean_dec(v_hi_532_);
                    lean_dec(v_lo_531_);
                    lean_dec_ref(v_lt_530_);
                    lean_dec(v_k_529_);
                    v___x_541_ = lean_box(0);
                    return v___x_541_;
                } else {
                    v___x_542_ = lean_nat_dec_lt(v_hi_532_, v___x_539_);
                    if v___x_542_ == 0 {
                        lean_dec(v_hi_532_);
                        v___x_543_ = lean_unsigned_to_nat(1);
                        v___x_544_ = lean_nat_sub(v___x_539_, v___x_543_);
                        v___y_534_ = v___x_544_;
                        state = 1;
                        continue;
                    } else {
                        v___y_534_ = v_hi_532_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_535_ = lean_nat_dec_le(v_lo_531_, v___y_534_);
                if v___x_535_ == 0 {
                    lean_dec(v___y_534_);
                    lean_dec(v_lo_531_);
                    lean_dec_ref(v_lt_530_);
                    lean_dec(v_k_529_);
                    v___x_536_ = lean_box(0);
                    return v___x_536_;
                } else {
                    v___x_537_ = l_Array_binSearch___redArg___closed__0;
                    v___x_538_ = l_Array_binSearchAux___redArg(
                        v_lt_530_, v___x_537_, v_as_528_, v_k_529_, v_lo_531_, v___y_534_,
                    );
                    return v___x_538_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearch___boxed(
    mut v_00_u03b1_545_: *mut LeanObject,
    mut v_as_546_: *mut LeanObject,
    mut v_k_547_: *mut LeanObject,
    mut v_lt_548_: *mut LeanObject,
    mut v_lo_549_: *mut LeanObject,
    mut v_hi_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_551_: *mut LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Array_binSearch(
        v_00_u03b1_545_,
        v_as_546_,
        v_k_547_,
        v_lt_548_,
        v_lo_549_,
        v_hi_550_,
    );
    lean_dec_ref(v_as_546_);
    return v_res_551_;
}
pub unsafe fn l_Array_binSearchContains___redArg(
    mut v_as_553_: *mut LeanObject,
    mut v_k_554_: *mut LeanObject,
    mut v_lt_555_: *mut LeanObject,
    mut v_lo_556_: *mut LeanObject,
    mut v_hi_557_: *mut LeanObject,
) -> u8 {
    let mut v___y_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: u8 = 0;
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_564_ = lean_array_get_size(v_as_553_);
                v___x_565_ = lean_nat_dec_lt(v_lo_556_, v___x_564_);
                if v___x_565_ == 0 {
                    lean_dec(v_hi_557_);
                    lean_dec(v_lo_556_);
                    lean_dec_ref(v_lt_555_);
                    lean_dec(v_k_554_);
                    return v___x_565_;
                } else {
                    v___x_566_ = lean_nat_dec_lt(v_hi_557_, v___x_564_);
                    if v___x_566_ == 0 {
                        lean_dec(v_hi_557_);
                        v___x_567_ = lean_unsigned_to_nat(1);
                        v___x_568_ = lean_nat_sub(v___x_564_, v___x_567_);
                        v___y_559_ = v___x_568_;
                        state = 1;
                        continue;
                    } else {
                        v___y_559_ = v_hi_557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_560_ = lean_nat_dec_le(v_lo_556_, v___y_559_);
                if v___x_560_ == 0 {
                    lean_dec(v___y_559_);
                    lean_dec(v_lo_556_);
                    lean_dec_ref(v_lt_555_);
                    lean_dec(v_k_554_);
                    return v___x_560_;
                } else {
                    v___x_561_ = l_Array_binSearchContains___redArg___closed__0;
                    v___x_562_ = l_Array_binSearchAux___redArg(
                        v_lt_555_, v___x_561_, v_as_553_, v_k_554_, v_lo_556_, v___y_559_,
                    );
                    v___x_563_ = (lean_unbox(v___x_562_) as u8);
                    lean_dec(v___x_562_);
                    return v___x_563_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchContains___redArg___boxed(
    mut v_as_569_: *mut LeanObject,
    mut v_k_570_: *mut LeanObject,
    mut v_lt_571_: *mut LeanObject,
    mut v_lo_572_: *mut LeanObject,
    mut v_hi_573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_574_: u8 = 0;
    let mut v_r_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_574_ =
        l_Array_binSearchContains___redArg(v_as_569_, v_k_570_, v_lt_571_, v_lo_572_, v_hi_573_);
    lean_dec_ref(v_as_569_);
    v_r_575_ = lean_box((v_res_574_) as usize);
    return v_r_575_;
}
pub unsafe fn l_Array_binSearchContains(
    mut v_00_u03b1_576_: *mut LeanObject,
    mut v_as_577_: *mut LeanObject,
    mut v_k_578_: *mut LeanObject,
    mut v_lt_579_: *mut LeanObject,
    mut v_lo_580_: *mut LeanObject,
    mut v_hi_581_: *mut LeanObject,
) -> u8 {
    let mut v___y_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: u8 = 0;
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_588_ = lean_array_get_size(v_as_577_);
                v___x_589_ = lean_nat_dec_lt(v_lo_580_, v___x_588_);
                if v___x_589_ == 0 {
                    lean_dec(v_hi_581_);
                    lean_dec(v_lo_580_);
                    lean_dec_ref(v_lt_579_);
                    lean_dec(v_k_578_);
                    return v___x_589_;
                } else {
                    v___x_590_ = lean_nat_dec_lt(v_hi_581_, v___x_588_);
                    if v___x_590_ == 0 {
                        lean_dec(v_hi_581_);
                        v___x_591_ = lean_unsigned_to_nat(1);
                        v___x_592_ = lean_nat_sub(v___x_588_, v___x_591_);
                        v___y_583_ = v___x_592_;
                        state = 1;
                        continue;
                    } else {
                        v___y_583_ = v_hi_581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_584_ = lean_nat_dec_le(v_lo_580_, v___y_583_);
                if v___x_584_ == 0 {
                    lean_dec(v___y_583_);
                    lean_dec(v_lo_580_);
                    lean_dec_ref(v_lt_579_);
                    lean_dec(v_k_578_);
                    return v___x_584_;
                } else {
                    v___x_585_ = l_Array_binSearchContains___redArg___closed__0;
                    v___x_586_ = l_Array_binSearchAux___redArg(
                        v_lt_579_, v___x_585_, v_as_577_, v_k_578_, v_lo_580_, v___y_583_,
                    );
                    v___x_587_ = (lean_unbox(v___x_586_) as u8);
                    lean_dec(v___x_586_);
                    return v___x_587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchContains___boxed(
    mut v_00_u03b1_593_: *mut LeanObject,
    mut v_as_594_: *mut LeanObject,
    mut v_k_595_: *mut LeanObject,
    mut v_lt_596_: *mut LeanObject,
    mut v_lo_597_: *mut LeanObject,
    mut v_hi_598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_599_: u8 = 0;
    let mut v_r_600_: *mut LeanObject = core::ptr::null_mut();
    v_res_599_ = l_Array_binSearchContains(
        v_00_u03b1_593_,
        v_as_594_,
        v_k_595_,
        v_lt_596_,
        v_lo_597_,
        v_hi_598_,
    );
    lean_dec_ref(v_as_594_);
    v_r_600_ = lean_box((v_res_599_) as usize);
    return v_r_600_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(
    mut v_toApplicative_601_: *mut LeanObject,
    mut v_xs_x27_602_: *mut LeanObject,
    mut v_mid_603_: *mut LeanObject,
    mut v_v_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_605_ = lean_ctor_get(v_toApplicative_601_, 1);
    lean_inc(v_toPure_605_);
    lean_dec_ref(v_toApplicative_601_);
    v___x_606_ = lean_array_fset(v_xs_x27_602_, v_mid_603_, v_v_604_);
    v___x_607_ = lean_apply_2(v_toPure_605_, lean_box(0), v___x_606_);
    return v___x_607_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed(
    mut v_toApplicative_608_: *mut LeanObject,
    mut v_xs_x27_609_: *mut LeanObject,
    mut v_mid_610_: *mut LeanObject,
    mut v_v_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_612_: *mut LeanObject = core::ptr::null_mut();
    v_res_612_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0(
        v_toApplicative_608_,
        v_xs_x27_609_,
        v_mid_610_,
        v_v_611_,
    );
    lean_dec(v_mid_610_);
    return v_res_612_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(
    mut v_toApplicative_613_: *mut LeanObject,
    mut v_x_614_: *mut LeanObject,
    mut v_as_615_: *mut LeanObject,
    mut v_v_616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_617_ = lean_ctor_get(v_toApplicative_613_, 1);
    lean_inc(v_toPure_617_);
    lean_dec_ref(v_toApplicative_613_);
    v___x_618_ = lean_unsigned_to_nat(1);
    v___x_619_ = lean_nat_add(v_x_614_, v___x_618_);
    v_j_620_ = lean_array_get_size(v_as_615_);
    v_as_621_ = lean_array_push(v_as_615_, v_v_616_);
    v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
        lean_box(0),
        v___x_619_,
        v_as_621_,
        v_j_620_,
    );
    lean_dec(v___x_619_);
    v___x_623_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_622_);
    return v___x_623_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed(
    mut v_toApplicative_624_: *mut LeanObject,
    mut v_x_625_: *mut LeanObject,
    mut v_as_626_: *mut LeanObject,
    mut v_v_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_628_: *mut LeanObject = core::ptr::null_mut();
    v_res_628_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1(
        v_toApplicative_624_,
        v_x_625_,
        v_as_626_,
        v_v_627_,
    );
    lean_dec(v_x_625_);
    return v_res_628_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(
    mut v_inst_629_: *mut LeanObject,
    mut v_lt_630_: *mut LeanObject,
    mut v_merge_631_: *mut LeanObject,
    mut v_add_632_: *mut LeanObject,
    mut v_as_633_: *mut LeanObject,
    mut v_k_634_: *mut LeanObject,
    mut v_x_635_: *mut LeanObject,
    mut v_x_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_midVal_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: u8 = 0;
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    let mut v_toApplicative_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v_toApplicative_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_637_ = lean_nat_add(v_x_635_, v_x_636_);
                v___x_638_ = lean_unsigned_to_nat(1);
                v_mid_639_ = lean_nat_shiftr(v___x_637_, v___x_638_);
                lean_dec(v___x_637_);
                v_midVal_640_ = lean_array_fget_borrowed(v_as_633_, v_mid_639_);
                lean_inc_ref(v_lt_630_);
                lean_inc(v_k_634_);
                lean_inc(v_midVal_640_);
                v___x_641_ = lean_apply_2(v_lt_630_, v_midVal_640_, v_k_634_);
                v___x_642_ = (lean_unbox(v___x_641_) as u8);
                if v___x_642_ == 0 {
                    lean_dec(v_x_636_);
                    lean_inc_ref(v_lt_630_);
                    lean_inc(v_midVal_640_);
                    lean_inc(v_k_634_);
                    v___x_643_ = lean_apply_2(v_lt_630_, v_k_634_, v_midVal_640_);
                    v___x_644_ = (lean_unbox(v___x_643_) as u8);
                    if v___x_644_ == 0 {
                        lean_dec(v_x_635_);
                        lean_dec(v_k_634_);
                        lean_dec(v_add_632_);
                        lean_dec_ref(v_lt_630_);
                        v___x_645_ = lean_array_get_size(v_as_633_);
                        v___x_646_ = lean_nat_dec_lt(v_mid_639_, v___x_645_);
                        if v___x_646_ == 0 {
                            lean_dec(v_mid_639_);
                            lean_dec(v_merge_631_);
                            v_toApplicative_647_ = lean_ctor_get(v_inst_629_, 0);
                            lean_inc_ref(v_toApplicative_647_);
                            lean_dec_ref(v_inst_629_);
                            v_toPure_648_ = lean_ctor_get(v_toApplicative_647_, 1);
                            lean_inc(v_toPure_648_);
                            lean_dec_ref(v_toApplicative_647_);
                            v___x_649_ = lean_apply_2(v_toPure_648_, lean_box(0), v_as_633_);
                            return v___x_649_;
                        } else {
                            lean_inc(v_midVal_640_);
                            v_toApplicative_650_ = lean_ctor_get(v_inst_629_, 0);
                            lean_inc_ref(v_toApplicative_650_);
                            v_toBind_651_ = lean_ctor_get(v_inst_629_, 1);
                            lean_inc(v_toBind_651_);
                            lean_dec_ref(v_inst_629_);
                            v___x_652_ = lean_box(0);
                            v_xs_x27_653_ = lean_array_fset(v_as_633_, v_mid_639_, v___x_652_);
                            v___f_654_ = lean_alloc_closure(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                            lean_closure_set(v___f_654_, 0, v_toApplicative_650_);
                            lean_closure_set(v___f_654_, 1, v_xs_x27_653_);
                            lean_closure_set(v___f_654_, 2, v_mid_639_);
                            v___x_655_ = lean_apply_1(v_merge_631_, v_midVal_640_);
                            v___x_656_ = lean_apply_4(
                                v_toBind_651_,
                                lean_box(0),
                                lean_box(0),
                                v___x_655_,
                                v___f_654_,
                            );
                            return v___x_656_;
                        }
                    } else {
                        v_x_636_ = v_mid_639_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_658_ = lean_nat_dec_eq(v_mid_639_, v_x_635_);
                    if v___x_658_ == 0 {
                        lean_dec(v_x_635_);
                        v_x_635_ = v_mid_639_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_mid_639_);
                        lean_dec(v_x_636_);
                        lean_dec(v_k_634_);
                        lean_dec(v_merge_631_);
                        lean_dec_ref(v_lt_630_);
                        v_toApplicative_660_ = lean_ctor_get(v_inst_629_, 0);
                        lean_inc_ref(v_toApplicative_660_);
                        v_toBind_661_ = lean_ctor_get(v_inst_629_, 1);
                        lean_inc(v_toBind_661_);
                        lean_dec_ref(v_inst_629_);
                        v___f_662_ = lean_alloc_closure(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_662_, 0, v_toApplicative_660_);
                        lean_closure_set(v___f_662_, 1, v_x_635_);
                        lean_closure_set(v___f_662_, 2, v_as_633_);
                        v___x_663_ = lean_box(0);
                        v___x_664_ = lean_apply_1(v_add_632_, v___x_663_);
                        v___x_665_ = lean_apply_4(
                            v_toBind_661_,
                            lean_box(0),
                            lean_box(0),
                            v___x_664_,
                            v___f_662_,
                        );
                        return v___x_665_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux(
    mut v_00_u03b1_666_: *mut LeanObject,
    mut v_m_667_: *mut LeanObject,
    mut v_inst_668_: *mut LeanObject,
    mut v_lt_669_: *mut LeanObject,
    mut v_merge_670_: *mut LeanObject,
    mut v_add_671_: *mut LeanObject,
    mut v_as_672_: *mut LeanObject,
    mut v_k_673_: *mut LeanObject,
    mut v_x_674_: *mut LeanObject,
    mut v_x_675_: *mut LeanObject,
    mut v_x_676_: *mut LeanObject,
    mut v_x_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_678_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(
        v_inst_668_,
        v_lt_669_,
        v_merge_670_,
        v_add_671_,
        v_as_672_,
        v_k_673_,
        v_x_674_,
        v_x_675_,
    );
    return v___x_678_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___redArg(
    mut v_x_679_: *mut LeanObject,
    mut v_x_680_: *mut LeanObject,
    mut v_h__1_681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___x_682_ = lean_apply_4(v_h__1_681_, v_x_679_, v_x_680_, lean_box(0), lean_box(0));
    return v___x_682_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(
    mut v_00_u03b1_683_: *mut LeanObject,
    mut v_lt_684_: *mut LeanObject,
    mut v_as_685_: *mut LeanObject,
    mut v_k_686_: *mut LeanObject,
    mut v_motive_687_: *mut LeanObject,
    mut v_x_688_: *mut LeanObject,
    mut v_x_689_: *mut LeanObject,
    mut v_x_690_: *mut LeanObject,
    mut v_x_691_: *mut LeanObject,
    mut v_h__1_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ = lean_apply_4(v_h__1_692_, v_x_688_, v_x_689_, lean_box(0), lean_box(0));
    return v___x_693_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter___boxed(
    mut v_00_u03b1_694_: *mut LeanObject,
    mut v_lt_695_: *mut LeanObject,
    mut v_as_696_: *mut LeanObject,
    mut v_k_697_: *mut LeanObject,
    mut v_motive_698_: *mut LeanObject,
    mut v_x_699_: *mut LeanObject,
    mut v_x_700_: *mut LeanObject,
    mut v_x_701_: *mut LeanObject,
    mut v_x_702_: *mut LeanObject,
    mut v_h__1_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux_match__1_splitter(
        v_00_u03b1_694_,
        v_lt_695_,
        v_as_696_,
        v_k_697_,
        v_motive_698_,
        v_x_699_,
        v_x_700_,
        v_x_701_,
        v_x_702_,
        v_h__1_703_,
    );
    lean_dec(v_k_697_);
    lean_dec_ref(v_as_696_);
    lean_dec_ref(v_lt_695_);
    return v_res_704_;
}
pub unsafe fn l_Array_binInsertM___redArg___lam__0(
    mut v_toApplicative_705_: *mut LeanObject,
    mut v_xs_x27_706_: *mut LeanObject,
    mut v___x_707_: *mut LeanObject,
    mut v_v_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_709_ = lean_ctor_get(v_toApplicative_705_, 1);
    lean_inc(v_toPure_709_);
    lean_dec_ref(v_toApplicative_705_);
    v___x_710_ = lean_array_fset(v_xs_x27_706_, v___x_707_, v_v_708_);
    v___x_711_ = lean_apply_2(v_toPure_709_, lean_box(0), v___x_710_);
    return v___x_711_;
}
pub unsafe fn l_Array_binInsertM___redArg___lam__0___boxed(
    mut v_toApplicative_712_: *mut LeanObject,
    mut v_xs_x27_713_: *mut LeanObject,
    mut v___x_714_: *mut LeanObject,
    mut v_v_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Array_binInsertM___redArg___lam__0(
        v_toApplicative_712_,
        v_xs_x27_713_,
        v___x_714_,
        v_v_715_,
    );
    lean_dec(v___x_714_);
    return v_res_716_;
}
pub unsafe fn l_Array_binInsertM___redArg___lam__2(
    mut v_toApplicative_717_: *mut LeanObject,
    mut v_as_718_: *mut LeanObject,
    mut v_v_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_720_ = lean_ctor_get(v_toApplicative_717_, 1);
    lean_inc(v_toPure_720_);
    lean_dec_ref(v_toApplicative_717_);
    v___x_721_ = lean_array_push(v_as_718_, v_v_719_);
    v___x_722_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_721_);
    return v___x_722_;
}
pub unsafe fn l_Array_binInsertM___redArg___lam__1(
    mut v_toApplicative_723_: *mut LeanObject,
    mut v_as_724_: *mut LeanObject,
    mut v___x_725_: *mut LeanObject,
    mut v___x_726_: *mut LeanObject,
    mut v_v_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_as_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_728_ = lean_ctor_get(v_toApplicative_723_, 1);
    lean_inc(v_toPure_728_);
    lean_dec_ref(v_toApplicative_723_);
    v_as_729_ = lean_array_push(v_as_724_, v_v_727_);
    v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
        lean_box(0),
        v___x_725_,
        v_as_729_,
        v___x_726_,
    );
    v___x_731_ = lean_apply_2(v_toPure_728_, lean_box(0), v___x_730_);
    return v___x_731_;
}
pub unsafe fn l_Array_binInsertM___redArg___lam__1___boxed(
    mut v_toApplicative_732_: *mut LeanObject,
    mut v_as_733_: *mut LeanObject,
    mut v___x_734_: *mut LeanObject,
    mut v___x_735_: *mut LeanObject,
    mut v_v_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_737_: *mut LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Array_binInsertM___redArg___lam__1(
        v_toApplicative_732_,
        v_as_733_,
        v___x_734_,
        v___x_735_,
        v_v_736_,
    );
    lean_dec(v___x_734_);
    return v_res_737_;
}
pub unsafe fn l_Array_binInsertM___redArg(
    mut v_inst_738_: *mut LeanObject,
    mut v_lt_739_: *mut LeanObject,
    mut v_merge_740_: *mut LeanObject,
    mut v_add_741_: *mut LeanObject,
    mut v_as_742_: *mut LeanObject,
    mut v_k_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    v___x_744_ = lean_array_get_size(v_as_742_);
    v___x_745_ = lean_unsigned_to_nat(0);
    v___x_746_ = lean_nat_dec_eq(v___x_744_, v___x_745_);
    if v___x_746_ == 0 {
        let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_749_: u8 = 0;
        v___x_747_ = lean_array_fget_borrowed(v_as_742_, v___x_745_);
        lean_inc_ref(v_lt_739_);
        lean_inc(v___x_747_);
        lean_inc(v_k_743_);
        v___x_748_ = lean_apply_2(v_lt_739_, v_k_743_, v___x_747_);
        v___x_749_ = (lean_unbox(v___x_748_) as u8);
        if v___x_749_ == 0 {
            let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_751_: u8 = 0;
            lean_inc_ref(v_lt_739_);
            lean_inc(v_k_743_);
            lean_inc(v___x_747_);
            v___x_750_ = lean_apply_2(v_lt_739_, v___x_747_, v_k_743_);
            v___x_751_ = (lean_unbox(v___x_750_) as u8);
            if v___x_751_ == 0 {
                let mut v___x_752_: u8 = 0;
                lean_dec(v_k_743_);
                lean_dec(v_add_741_);
                lean_dec_ref(v_lt_739_);
                v___x_752_ = lean_nat_dec_lt(v___x_745_, v___x_744_);
                if v___x_752_ == 0 {
                    let mut v_toApplicative_753_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toPure_754_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_merge_740_);
                    v_toApplicative_753_ = lean_ctor_get(v_inst_738_, 0);
                    lean_inc_ref(v_toApplicative_753_);
                    lean_dec_ref(v_inst_738_);
                    v_toPure_754_ = lean_ctor_get(v_toApplicative_753_, 1);
                    lean_inc(v_toPure_754_);
                    lean_dec_ref(v_toApplicative_753_);
                    v___x_755_ = lean_apply_2(v_toPure_754_, lean_box(0), v_as_742_);
                    return v___x_755_;
                } else {
                    let mut v_toApplicative_756_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toBind_757_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_759_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___f_760_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc(v___x_747_);
                    v_toApplicative_756_ = lean_ctor_get(v_inst_738_, 0);
                    lean_inc_ref(v_toApplicative_756_);
                    v_toBind_757_ = lean_ctor_get(v_inst_738_, 1);
                    lean_inc(v_toBind_757_);
                    lean_dec_ref(v_inst_738_);
                    v___x_758_ = lean_box(0);
                    v_xs_x27_759_ = lean_array_fset(v_as_742_, v___x_745_, v___x_758_);
                    v___f_760_ = lean_alloc_closure(
                        l_Array_binInsertM___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_760_, 0, v_toApplicative_756_);
                    lean_closure_set(v___f_760_, 1, v_xs_x27_759_);
                    lean_closure_set(v___f_760_, 2, v___x_745_);
                    v___x_761_ = lean_apply_1(v_merge_740_, v___x_747_);
                    v___x_762_ = lean_apply_4(
                        v_toBind_757_,
                        lean_box(0),
                        lean_box(0),
                        v___x_761_,
                        v___f_760_,
                    );
                    return v___x_762_;
                }
            } else {
                let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_767_: u8 = 0;
                v___x_763_ = lean_unsigned_to_nat(1);
                v___x_764_ = lean_nat_sub(v___x_744_, v___x_763_);
                v___x_765_ = lean_array_fget_borrowed(v_as_742_, v___x_764_);
                lean_inc_ref(v_lt_739_);
                lean_inc(v_k_743_);
                lean_inc(v___x_765_);
                v___x_766_ = lean_apply_2(v_lt_739_, v___x_765_, v_k_743_);
                v___x_767_ = (lean_unbox(v___x_766_) as u8);
                if v___x_767_ == 0 {
                    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_769_: u8 = 0;
                    lean_inc_ref(v_lt_739_);
                    lean_inc(v___x_765_);
                    lean_inc(v_k_743_);
                    v___x_768_ = lean_apply_2(v_lt_739_, v_k_743_, v___x_765_);
                    v___x_769_ = (lean_unbox(v___x_768_) as u8);
                    if v___x_769_ == 0 {
                        let mut v___x_770_: u8 = 0;
                        lean_dec(v_k_743_);
                        lean_dec(v_add_741_);
                        lean_dec_ref(v_lt_739_);
                        v___x_770_ = lean_nat_dec_lt(v___x_764_, v___x_744_);
                        if v___x_770_ == 0 {
                            let mut v_toApplicative_771_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_toPure_772_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v___x_764_);
                            lean_dec(v_merge_740_);
                            v_toApplicative_771_ = lean_ctor_get(v_inst_738_, 0);
                            lean_inc_ref(v_toApplicative_771_);
                            lean_dec_ref(v_inst_738_);
                            v_toPure_772_ = lean_ctor_get(v_toApplicative_771_, 1);
                            lean_inc(v_toPure_772_);
                            lean_dec_ref(v_toApplicative_771_);
                            v___x_773_ = lean_apply_2(v_toPure_772_, lean_box(0), v_as_742_);
                            return v___x_773_;
                        } else {
                            let mut v_toApplicative_774_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_toBind_775_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_xs_x27_777_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___f_778_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
                            lean_inc(v___x_765_);
                            v_toApplicative_774_ = lean_ctor_get(v_inst_738_, 0);
                            lean_inc_ref(v_toApplicative_774_);
                            v_toBind_775_ = lean_ctor_get(v_inst_738_, 1);
                            lean_inc(v_toBind_775_);
                            lean_dec_ref(v_inst_738_);
                            v___x_776_ = lean_box(0);
                            v_xs_x27_777_ = lean_array_fset(v_as_742_, v___x_764_, v___x_776_);
                            v___f_778_ = lean_alloc_closure(
                                l_Array_binInsertM___redArg___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                4,
                                3,
                            );
                            lean_closure_set(v___f_778_, 0, v_toApplicative_774_);
                            lean_closure_set(v___f_778_, 1, v_xs_x27_777_);
                            lean_closure_set(v___f_778_, 2, v___x_764_);
                            v___x_779_ = lean_apply_1(v_merge_740_, v___x_765_);
                            v___x_780_ = lean_apply_4(
                                v_toBind_775_,
                                lean_box(0),
                                lean_box(0),
                                v___x_779_,
                                v___f_778_,
                            );
                            return v___x_780_;
                        }
                    } else {
                        let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
                        v___x_781_ =
                            l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___redArg(
                                v_inst_738_,
                                v_lt_739_,
                                v_merge_740_,
                                v_add_741_,
                                v_as_742_,
                                v_k_743_,
                                v___x_745_,
                                v___x_764_,
                            );
                        return v___x_781_;
                    }
                } else {
                    let mut v_toApplicative_782_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_toBind_783_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___f_784_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_764_);
                    lean_dec(v_k_743_);
                    lean_dec(v_merge_740_);
                    lean_dec_ref(v_lt_739_);
                    v_toApplicative_782_ = lean_ctor_get(v_inst_738_, 0);
                    lean_inc_ref(v_toApplicative_782_);
                    v_toBind_783_ = lean_ctor_get(v_inst_738_, 1);
                    lean_inc(v_toBind_783_);
                    lean_dec_ref(v_inst_738_);
                    v___f_784_ = lean_alloc_closure(
                        l_Array_binInsertM___redArg___lam__2 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_784_, 0, v_toApplicative_782_);
                    lean_closure_set(v___f_784_, 1, v_as_742_);
                    v___x_785_ = lean_box(0);
                    v___x_786_ = lean_apply_1(v_add_741_, v___x_785_);
                    v___x_787_ = lean_apply_4(
                        v_toBind_783_,
                        lean_box(0),
                        lean_box(0),
                        v___x_786_,
                        v___f_784_,
                    );
                    return v___x_787_;
                }
            }
        } else {
            let mut v_toApplicative_788_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_789_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_790_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_k_743_);
            lean_dec(v_merge_740_);
            lean_dec_ref(v_lt_739_);
            v_toApplicative_788_ = lean_ctor_get(v_inst_738_, 0);
            lean_inc_ref(v_toApplicative_788_);
            v_toBind_789_ = lean_ctor_get(v_inst_738_, 1);
            lean_inc(v_toBind_789_);
            lean_dec_ref(v_inst_738_);
            v___f_790_ = lean_alloc_closure(
                l_Array_binInsertM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_790_, 0, v_toApplicative_788_);
            lean_closure_set(v___f_790_, 1, v_as_742_);
            lean_closure_set(v___f_790_, 2, v___x_745_);
            lean_closure_set(v___f_790_, 3, v___x_744_);
            v___x_791_ = lean_box(0);
            v___x_792_ = lean_apply_1(v_add_741_, v___x_791_);
            v___x_793_ = lean_apply_4(
                v_toBind_789_,
                lean_box(0),
                lean_box(0),
                v___x_792_,
                v___f_790_,
            );
            return v___x_793_;
        }
    } else {
        let mut v_toApplicative_794_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_743_);
        lean_dec(v_merge_740_);
        lean_dec_ref(v_lt_739_);
        v_toApplicative_794_ = lean_ctor_get(v_inst_738_, 0);
        lean_inc_ref(v_toApplicative_794_);
        v_toBind_795_ = lean_ctor_get(v_inst_738_, 1);
        lean_inc(v_toBind_795_);
        lean_dec_ref(v_inst_738_);
        v___f_796_ = lean_alloc_closure(
            l_Array_binInsertM___redArg___lam__2 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_796_, 0, v_toApplicative_794_);
        lean_closure_set(v___f_796_, 1, v_as_742_);
        v___x_797_ = lean_box(0);
        v___x_798_ = lean_apply_1(v_add_741_, v___x_797_);
        v___x_799_ = lean_apply_4(
            v_toBind_795_,
            lean_box(0),
            lean_box(0),
            v___x_798_,
            v___f_796_,
        );
        return v___x_799_;
    }
}
pub unsafe fn l_Array_binInsertM(
    mut v_00_u03b1_800_: *mut LeanObject,
    mut v_m_801_: *mut LeanObject,
    mut v_inst_802_: *mut LeanObject,
    mut v_lt_803_: *mut LeanObject,
    mut v_merge_804_: *mut LeanObject,
    mut v_add_805_: *mut LeanObject,
    mut v_as_806_: *mut LeanObject,
    mut v_k_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_808_ = l_Array_binInsertM___redArg(
        v_inst_802_,
        v_lt_803_,
        v_merge_804_,
        v_add_805_,
        v_as_806_,
        v_k_807_,
    );
    return v___x_808_;
}
pub unsafe fn l_Array_binInsert___redArg___lam__0(
    mut v_k_809_: *mut LeanObject,
    mut v_x_810_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_809_);
    return v_k_809_;
}
pub unsafe fn l_Array_binInsert___redArg___lam__0___boxed(
    mut v_k_811_: *mut LeanObject,
    mut v_x_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Array_binInsert___redArg___lam__0(v_k_811_, v_x_812_);
    lean_dec(v_x_812_);
    lean_dec(v_k_811_);
    return v_res_813_;
}
pub unsafe fn l_Array_binInsert___redArg___lam__1(
    mut v_k_814_: *mut LeanObject,
    mut v_x_815_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_814_);
    return v_k_814_;
}
pub unsafe fn l_Array_binInsert___redArg___lam__1___boxed(
    mut v_k_816_: *mut LeanObject,
    mut v_x_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_818_: *mut LeanObject = core::ptr::null_mut();
    v_res_818_ = l_Array_binInsert___redArg___lam__1(v_k_816_, v_x_817_);
    lean_dec(v_k_816_);
    return v_res_818_;
}
pub unsafe fn l_Array_binInsert___redArg(
    mut v_lt_838_: *mut LeanObject,
    mut v_as_839_: *mut LeanObject,
    mut v_k_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_k_840_, 2);
    v___f_841_ = lean_alloc_closure(
        l_Array_binInsert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_841_, 0, v_k_840_);
    v___f_842_ = lean_alloc_closure(
        l_Array_binInsert___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_842_, 0, v_k_840_);
    v___x_843_ = l_Array_binInsert___redArg___closed__9;
    v___x_844_ = l_Array_binInsertM___redArg(
        v___x_843_, v_lt_838_, v___f_841_, v___f_842_, v_as_839_, v_k_840_,
    );
    return v___x_844_;
}
pub unsafe fn l_Array_binInsert(
    mut v_00_u03b1_845_: *mut LeanObject,
    mut v_lt_846_: *mut LeanObject,
    mut v_as_847_: *mut LeanObject,
    mut v_k_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_k_848_, 2);
    v___f_849_ = lean_alloc_closure(
        l_Array_binInsert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_849_, 0, v_k_848_);
    v___f_850_ = lean_alloc_closure(
        l_Array_binInsert___redArg___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_850_, 0, v_k_848_);
    v___x_851_ = l_Array_binInsert___redArg___closed__9;
    v___x_852_ = l_Array_binInsertM___redArg(
        v___x_851_, v_lt_846_, v___f_849_, v___f_850_, v_as_847_, v_k_848_,
    );
    return v___x_852_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_BinSearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_BinSearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_BinSearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_BinSearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_BinSearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_BinSearch(builtin);
}
