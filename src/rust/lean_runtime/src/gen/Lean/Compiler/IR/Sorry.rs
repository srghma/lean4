// Lean compiler output
// Module: Lean.Compiler.IR.Sorry
// Imports: Lean.Compiler.IR.CompilerM
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Compiler::IR::Basic::{
    l_Lean_IR_Alt_body, l_Lean_IR_FnBody_body, l_Lean_IR_FnBody_isTerminal,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, l_Lean_IR_findDecl___redArg,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 111, 114, 114, 121, 65, 120, 0]};
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value) as *mut LeanObject,5207765522374246084 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_updateSorryDep___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_updateSorryDep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_updateSorryDep___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
    mut v_f_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_g_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: u8 = 0;
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v_localSorryMap_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___y_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_a_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_425_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
                v___x_426_ = lean_name_eq(v_f_410_, v___x_425_);
                if v___x_426_ == 0 {
                    v_localSorryMap_427_ = lean_ctor_get(v_a_411_, 0);
                    v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_427_, v_f_410_);
                    if lean_obj_tag(v___x_428_) == 1 {
                        v_val_429_ = lean_ctor_get(v___x_428_, 0);
                        lean_inc(v_val_429_);
                        lean_dec_ref_known(v___x_428_, 1);
                        v_g_415_ = v_val_429_;
                        v___y_416_ = v_a_411_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_428_);
                        lean_inc(v_f_410_);
                        v___x_430_ = l_Lean_IR_findDecl___redArg(v_f_410_, v_a_412_);
                        if lean_obj_tag(v___x_430_) == 0 {
                            v_a_431_ = lean_ctor_get(v___x_430_, 0);
                            v_isSharedCheck_445_ = (!lean_is_exclusive(v___x_430_)) as u8;
                            if v_isSharedCheck_445_ == 0 {
                                v___x_433_ = v___x_430_;
                                v_isShared_434_ = v_isSharedCheck_445_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_431_);
                                lean_dec(v___x_430_);
                                v___x_433_ = lean_box(0);
                                v_isShared_434_ = v_isSharedCheck_445_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_a_411_);
                            lean_dec(v_f_410_);
                            v_a_446_ = lean_ctor_get(v___x_430_, 0);
                            v_isSharedCheck_453_ = (!lean_is_exclusive(v___x_430_)) as u8;
                            if v_isSharedCheck_453_ == 0 {
                                v___x_448_ = v___x_430_;
                                v_isShared_449_ = v_isSharedCheck_453_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_446_);
                                lean_dec(v___x_430_);
                                v___x_448_ = lean_box(0);
                                v_isShared_449_ = v_isSharedCheck_453_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_454_, 0, v_f_410_);
                    v___x_455_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_455_, 0, v___x_454_);
                    lean_ctor_set(v___x_455_, 1, v_a_411_);
                    v___x_456_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_456_, 0, v___x_455_);
                    return v___x_456_;
                }
            }
            1 => {
                v___x_417_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
                v___x_418_ = lean_name_eq(v_g_415_, v___x_417_);
                if v___x_418_ == 0 {
                    lean_dec(v_f_410_);
                    v___x_419_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_419_, 0, v_g_415_);
                    v___x_420_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_420_, 0, v___x_419_);
                    lean_ctor_set(v___x_420_, 1, v___y_416_);
                    v___x_421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_421_, 0, v___x_420_);
                    return v___x_421_;
                } else {
                    lean_dec(v_g_415_);
                    v___x_422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_422_, 0, v_f_410_);
                    v___x_423_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_423_, 0, v___x_422_);
                    lean_ctor_set(v___x_423_, 1, v___y_416_);
                    v___x_424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_424_, 0, v___x_423_);
                    return v___x_424_;
                }
            }
            2 => {
                if lean_obj_tag(v_a_431_) == 1 {
                    v_val_442_ = lean_ctor_get(v_a_431_, 0);
                    lean_inc(v_val_442_);
                    lean_dec_ref_known(v_a_431_, 1);
                    if lean_obj_tag(v_val_442_) == 0 {
                        v_info_443_ = lean_ctor_get(v_val_442_, 4);
                        lean_inc(v_info_443_);
                        lean_dec_ref_known(v_val_442_, 5);
                        if lean_obj_tag(v_info_443_) == 1 {
                            lean_del_object(v___x_433_);
                            v_val_444_ = lean_ctor_get(v_info_443_, 0);
                            lean_inc(v_val_444_);
                            lean_dec_ref_known(v_info_443_, 1);
                            v_g_415_ = v_val_444_;
                            v___y_416_ = v_a_411_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_info_443_);
                            lean_dec(v_f_410_);
                            v___y_436_ = v_a_411_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_442_);
                        lean_dec(v_f_410_);
                        v___y_436_ = v_a_411_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_431_);
                    lean_dec(v_f_410_);
                    v___y_436_ = v_a_411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_437_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                v___x_438_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_438_, 0, v___x_437_);
                lean_ctor_set(v___x_438_, 1, v___y_436_);
                if v_isShared_434_ == 0 {
                    lean_ctor_set(v___x_433_, 0, v___x_438_);
                    v___x_440_ = v___x_433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_440_;
            }
            5 => {
                if v_isShared_449_ == 0 {
                    v___x_451_ = v___x_448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
                    v___x_451_ = v_reuseFailAlloc_452_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___boxed(
    mut v_f_457_: *mut LeanObject,
    mut v_a_458_: *mut LeanObject,
    mut v_a_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_461_: *mut LeanObject = core::ptr::null_mut();
    v_res_461_ =
        l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
            v_f_457_, v_a_458_, v_a_459_,
        );
    lean_dec(v_a_459_);
    return v_res_461_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(
    mut v_f_462_: *mut LeanObject,
    mut v_a_463_: *mut LeanObject,
    mut v_a_464_: *mut LeanObject,
    mut v_a_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ =
        l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
            v_f_462_, v_a_463_, v_a_465_,
        );
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(
    mut v_f_468_: *mut LeanObject,
    mut v_a_469_: *mut LeanObject,
    mut v_a_470_: *mut LeanObject,
    mut v_a_471_: *mut LeanObject,
    mut v_a_472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_473_: *mut LeanObject = core::ptr::null_mut();
    v_res_473_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(
        v_f_468_, v_a_469_, v_a_470_, v_a_471_,
    );
    lean_dec(v_a_471_);
    lean_dec_ref(v_a_470_);
    return v_res_473_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___redArg(
    mut v_x_474_: *mut LeanObject,
    mut v_a_475_: *mut LeanObject,
    mut v_a_476_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_474_) {
        6 => {
            let mut v_c_478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
            v_c_478_ = lean_ctor_get(v_x_474_, 0);
            lean_inc(v_c_478_);
            lean_dec_ref_known(v_x_474_, 2);
            v___x_479_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_478_, v_a_475_, v_a_476_);
            return v___x_479_;
        }
        7 => {
            let mut v_c_480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
            v_c_480_ = lean_ctor_get(v_x_474_, 0);
            lean_inc(v_c_480_);
            lean_dec_ref_known(v_x_474_, 2);
            v___x_481_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_480_, v_a_475_, v_a_476_);
            return v___x_481_;
        }
        _ => {
            let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_474_);
            v___x_482_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
            v___x_483_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_483_, 0, v___x_482_);
            lean_ctor_set(v___x_483_, 1, v_a_475_);
            v___x_484_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_484_, 0, v___x_483_);
            return v___x_484_;
        }
    }
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___redArg___boxed(
    mut v_x_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_489_: *mut LeanObject = core::ptr::null_mut();
    v_res_489_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_485_, v_a_486_, v_a_487_);
    lean_dec(v_a_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr(
    mut v_x_490_: *mut LeanObject,
    mut v_a_491_: *mut LeanObject,
    mut v_a_492_: *mut LeanObject,
    mut v_a_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_490_, v_a_491_, v_a_493_);
    return v___x_495_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___boxed(
    mut v_x_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
    mut v_a_498_: *mut LeanObject,
    mut v_a_499_: *mut LeanObject,
    mut v_a_500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_501_: *mut LeanObject = core::ptr::null_mut();
    v_res_501_ = l_Lean_IR_Sorry_visitExpr(v_x_496_, v_a_497_, v_a_498_, v_a_499_);
    lean_dec(v_a_499_);
    lean_dec_ref(v_a_498_);
    return v_res_501_;
}
pub unsafe fn l_Lean_IR_Sorry_visitFnBody(
    mut v_b_502_: *mut LeanObject,
    mut v_a_503_: *mut LeanObject,
    mut v_a_504_: *mut LeanObject,
    mut v_a_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u8 = 0;
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: usize = 0;
    let mut v___x_534_: usize = 0;
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: usize = 0;
    let mut v___x_537_: usize = 0;
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_b_502_) {
                0 => {
                    v_e_507_ = lean_ctor_get(v_b_502_, 2);
                    lean_inc_ref(v_e_507_);
                    v_b_508_ = lean_ctor_get(v_b_502_, 3);
                    lean_inc(v_b_508_);
                    lean_dec_ref_known(v_b_502_, 4);
                    v___x_509_ = l_Lean_IR_Sorry_visitExpr___redArg(v_e_507_, v_a_503_, v_a_505_);
                    if lean_obj_tag(v___x_509_) == 0 {
                        v_a_510_ = lean_ctor_get(v___x_509_, 0);
                        lean_inc(v_a_510_);
                        v_fst_511_ = lean_ctor_get(v_a_510_, 0);
                        if lean_obj_tag(v_fst_511_) == 0 {
                            lean_dec(v_a_510_);
                            lean_dec(v_b_508_);
                            return v___x_509_;
                        } else {
                            lean_dec_ref_known(v___x_509_, 1);
                            v_snd_512_ = lean_ctor_get(v_a_510_, 1);
                            lean_inc(v_snd_512_);
                            lean_dec(v_a_510_);
                            v_b_502_ = v_b_508_;
                            v_a_503_ = v_snd_512_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_508_);
                        return v___x_509_;
                    }
                }
                1 => {
                    v_v_514_ = lean_ctor_get(v_b_502_, 2);
                    lean_inc(v_v_514_);
                    v_b_515_ = lean_ctor_get(v_b_502_, 3);
                    lean_inc(v_b_515_);
                    lean_dec_ref_known(v_b_502_, 4);
                    v___x_516_ =
                        l_Lean_IR_Sorry_visitFnBody(v_v_514_, v_a_503_, v_a_504_, v_a_505_);
                    if lean_obj_tag(v___x_516_) == 0 {
                        v_a_517_ = lean_ctor_get(v___x_516_, 0);
                        lean_inc(v_a_517_);
                        v_fst_518_ = lean_ctor_get(v_a_517_, 0);
                        if lean_obj_tag(v_fst_518_) == 0 {
                            lean_dec(v_a_517_);
                            lean_dec(v_b_515_);
                            return v___x_516_;
                        } else {
                            lean_dec_ref_known(v___x_516_, 1);
                            v_snd_519_ = lean_ctor_get(v_a_517_, 1);
                            lean_inc(v_snd_519_);
                            lean_dec(v_a_517_);
                            v_b_502_ = v_b_515_;
                            v_a_503_ = v_snd_519_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_515_);
                        return v___x_516_;
                    }
                }
                9 => {
                    v_cs_521_ = lean_ctor_get(v_b_502_, 3);
                    lean_inc_ref(v_cs_521_);
                    lean_dec_ref_known(v_b_502_, 4);
                    v___x_522_ = lean_unsigned_to_nat(0);
                    v___x_523_ = lean_array_get_size(v_cs_521_);
                    v___x_524_ = lean_box(0);
                    v___x_525_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
                    if v___x_525_ == 0 {
                        lean_dec_ref(v_cs_521_);
                        v___x_526_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                        v___x_527_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_527_, 0, v___x_526_);
                        lean_ctor_set(v___x_527_, 1, v_a_503_);
                        v___x_528_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_528_, 0, v___x_527_);
                        return v___x_528_;
                    } else {
                        v___x_529_ = lean_nat_dec_le(v___x_523_, v___x_523_);
                        if v___x_529_ == 0 {
                            if v___x_525_ == 0 {
                                lean_dec_ref(v_cs_521_);
                                v___x_530_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                                v___x_531_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_531_, 0, v___x_530_);
                                lean_ctor_set(v___x_531_, 1, v_a_503_);
                                v___x_532_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_532_, 0, v___x_531_);
                                return v___x_532_;
                            } else {
                                v___x_533_ = 0usize;
                                v___x_534_ = lean_usize_of_nat(v___x_523_);
                                v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_521_, v___x_533_, v___x_534_, v___x_524_, v_a_503_, v_a_504_, v_a_505_);
                                lean_dec_ref(v_cs_521_);
                                return v___x_535_;
                            }
                        } else {
                            v___x_536_ = 0usize;
                            v___x_537_ = lean_usize_of_nat(v___x_523_);
                            v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_521_, v___x_536_, v___x_537_, v___x_524_, v_a_503_, v_a_504_, v_a_505_);
                            lean_dec_ref(v_cs_521_);
                            return v___x_538_;
                        }
                    }
                }
                _ => {
                    v___x_539_ = l_Lean_IR_FnBody_isTerminal(v_b_502_);
                    if v___x_539_ == 0 {
                        v___x_540_ = l_Lean_IR_FnBody_body(v_b_502_);
                        lean_dec(v_b_502_);
                        v_b_502_ = v___x_540_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_b_502_);
                        v___x_542_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                        v___x_543_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_543_, 0, v___x_542_);
                        lean_ctor_set(v___x_543_, 1, v_a_503_);
                        v___x_544_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_544_, 0, v___x_543_);
                        return v___x_544_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(
    mut v_as_545_: *mut LeanObject,
    mut v_i_546_: usize,
    mut v_stop_547_: usize,
    mut v_b_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
    mut v___y_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: usize = 0;
    let mut v___x_562_: usize = 0;
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_553_ = lean_usize_dec_eq(v_i_546_, v_stop_547_);
                if v___x_553_ == 0 {
                    v___x_554_ = lean_array_uget_borrowed(v_as_545_, v_i_546_);
                    v___x_555_ = l_Lean_IR_Alt_body(v___x_554_);
                    v___x_556_ =
                        l_Lean_IR_Sorry_visitFnBody(v___x_555_, v___y_549_, v___y_550_, v___y_551_);
                    if lean_obj_tag(v___x_556_) == 0 {
                        v_a_557_ = lean_ctor_get(v___x_556_, 0);
                        lean_inc(v_a_557_);
                        v_fst_558_ = lean_ctor_get(v_a_557_, 0);
                        lean_inc(v_fst_558_);
                        if lean_obj_tag(v_fst_558_) == 0 {
                            lean_dec_ref_known(v_fst_558_, 1);
                            lean_dec(v_a_557_);
                            return v___x_556_;
                        } else {
                            lean_dec_ref_known(v___x_556_, 1);
                            v_snd_559_ = lean_ctor_get(v_a_557_, 1);
                            lean_inc(v_snd_559_);
                            lean_dec(v_a_557_);
                            v_a_560_ = lean_ctor_get(v_fst_558_, 0);
                            lean_inc(v_a_560_);
                            lean_dec_ref_known(v_fst_558_, 1);
                            v___x_561_ = 1usize;
                            v___x_562_ = lean_usize_add(v_i_546_, v___x_561_);
                            v_i_546_ = v___x_562_;
                            v_b_548_ = v_a_560_;
                            v___y_549_ = v_snd_559_;
                            state = 0;
                            continue;
                        }
                    } else {
                        return v___x_556_;
                    }
                } else {
                    v___x_564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_564_, 0, v_b_548_);
                    v___x_565_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_565_, 0, v___x_564_);
                    lean_ctor_set(v___x_565_, 1, v___y_549_);
                    v___x_566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_566_, 0, v___x_565_);
                    return v___x_566_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(
    mut v_as_567_: *mut LeanObject,
    mut v_i_568_: *mut LeanObject,
    mut v_stop_569_: *mut LeanObject,
    mut v_b_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_575_: usize = 0;
    let mut v_stop_boxed_576_: usize = 0;
    let mut v_res_577_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_575_ = lean_unbox_usize(v_i_568_);
    lean_dec(v_i_568_);
    v_stop_boxed_576_ = lean_unbox_usize(v_stop_569_);
    lean_dec(v_stop_569_);
    v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_567_, v_i_boxed_575_, v_stop_boxed_576_, v_b_570_, v___y_571_, v___y_572_, v___y_573_);
    lean_dec(v___y_573_);
    lean_dec_ref(v___y_572_);
    lean_dec_ref(v_as_567_);
    return v_res_577_;
}
pub unsafe fn l_Lean_IR_Sorry_visitFnBody___boxed(
    mut v_b_578_: *mut LeanObject,
    mut v_a_579_: *mut LeanObject,
    mut v_a_580_: *mut LeanObject,
    mut v_a_581_: *mut LeanObject,
    mut v_a_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_583_: *mut LeanObject = core::ptr::null_mut();
    v_res_583_ = l_Lean_IR_Sorry_visitFnBody(v_b_578_, v_a_579_, v_a_580_, v_a_581_);
    lean_dec(v_a_581_);
    lean_dec_ref(v_a_580_);
    return v_res_583_;
}
pub unsafe fn l_Lean_IR_Sorry_visitDecl(
    mut v_d_584_: *mut LeanObject,
    mut v_a_585_: *mut LeanObject,
    mut v_a_586_: *mut LeanObject,
    mut v_a_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_597_: u8 = 0;
    let mut v_fst_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v_a_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut v_unused_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_634_: u8 = 0;
    let mut v_unused_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_636_: u8 = 0;
    let mut v_a_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut v_unused_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_d_584_) == 0 {
                    v_f_589_ = lean_ctor_get(v_d_584_, 0);
                    lean_inc(v_f_589_);
                    v_body_590_ = lean_ctor_get(v_d_584_, 3);
                    lean_inc(v_body_590_);
                    lean_dec_ref_known(v_d_584_, 5);
                    v_localSorryMap_591_ = lean_ctor_get(v_a_585_, 0);
                    v___x_592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_591_, v_f_589_);
                    if lean_obj_tag(v___x_592_) == 0 {
                        v___x_593_ =
                            l_Lean_IR_Sorry_visitFnBody(v_body_590_, v_a_585_, v_a_586_, v_a_587_);
                        if lean_obj_tag(v___x_593_) == 0 {
                            v_a_594_ = lean_ctor_get(v___x_593_, 0);
                            v_isSharedCheck_636_ = (!lean_is_exclusive(v___x_593_)) as u8;
                            if v_isSharedCheck_636_ == 0 {
                                v___x_596_ = v___x_593_;
                                v_isShared_597_ = v_isSharedCheck_636_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_594_);
                                lean_dec(v___x_593_);
                                v___x_596_ = lean_box(0);
                                v_isShared_597_ = v_isSharedCheck_636_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_f_589_);
                            v_a_637_ = lean_ctor_get(v___x_593_, 0);
                            v_isSharedCheck_644_ = (!lean_is_exclusive(v___x_593_)) as u8;
                            if v_isSharedCheck_644_ == 0 {
                                v___x_639_ = v___x_593_;
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_637_);
                                lean_dec(v___x_593_);
                                v___x_639_ = lean_box(0);
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_body_590_);
                        lean_dec(v_f_589_);
                        v_isSharedCheck_653_ = (!lean_is_exclusive(v___x_592_)) as u8;
                        if v_isSharedCheck_653_ == 0 {
                            v_unused_654_ = lean_ctor_get(v___x_592_, 0);
                            lean_dec(v_unused_654_);
                            v___x_646_ = v___x_592_;
                            v_isShared_647_ = v_isSharedCheck_653_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v___x_592_);
                            v___x_646_ = lean_box(0);
                            v_isShared_647_ = v_isSharedCheck_653_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_d_584_);
                    v___x_655_ = lean_box(0);
                    v___x_656_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_656_, 0, v___x_655_);
                    lean_ctor_set(v___x_656_, 1, v_a_585_);
                    v___x_657_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_657_, 0, v___x_656_);
                    return v___x_657_;
                }
            }
            1 => {
                v_fst_598_ = lean_ctor_get(v_a_594_, 0);
                if lean_obj_tag(v_fst_598_) == 0 {
                    lean_inc_ref(v_fst_598_);
                    v_snd_599_ = lean_ctor_get(v_a_594_, 1);
                    v_isSharedCheck_621_ = (!lean_is_exclusive(v_a_594_)) as u8;
                    if v_isSharedCheck_621_ == 0 {
                        v_unused_622_ = lean_ctor_get(v_a_594_, 0);
                        lean_dec(v_unused_622_);
                        v___x_601_ = v_a_594_;
                        v_isShared_602_ = v_isSharedCheck_621_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_599_);
                        lean_dec(v_a_594_);
                        v___x_601_ = lean_box(0);
                        v_isShared_602_ = v_isSharedCheck_621_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_f_589_);
                    v_snd_623_ = lean_ctor_get(v_a_594_, 1);
                    v_isSharedCheck_634_ = (!lean_is_exclusive(v_a_594_)) as u8;
                    if v_isSharedCheck_634_ == 0 {
                        v_unused_635_ = lean_ctor_get(v_a_594_, 0);
                        lean_dec(v_unused_635_);
                        v___x_625_ = v_a_594_;
                        v_isShared_626_ = v_isSharedCheck_634_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_623_);
                        lean_dec(v_a_594_);
                        v___x_625_ = lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_634_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_a_603_ = lean_ctor_get(v_fst_598_, 0);
                lean_inc(v_a_603_);
                lean_dec_ref_known(v_fst_598_, 1);
                v_localSorryMap_604_ = lean_ctor_get(v_snd_599_, 0);
                v_isSharedCheck_620_ = (!lean_is_exclusive(v_snd_599_)) as u8;
                if v_isSharedCheck_620_ == 0 {
                    v___x_606_ = v_snd_599_;
                    v_isShared_607_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_localSorryMap_604_);
                    lean_dec(v_snd_599_);
                    v___x_606_ = lean_box(0);
                    v_isShared_607_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_608_ = lean_box(0);
                v___x_609_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_589_, v_a_603_, v_localSorryMap_604_);
                v___x_610_ = 1;
                if v_isShared_607_ == 0 {
                    lean_ctor_set(v___x_606_, 0, v___x_609_);
                    v___x_612_ = v___x_606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_609_);
                    v___x_612_ = v_reuseFailAlloc_619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_610_,
                );
                if v_isShared_602_ == 0 {
                    lean_ctor_set(v___x_601_, 1, v___x_612_);
                    lean_ctor_set(v___x_601_, 0, v___x_608_);
                    v___x_614_ = v___x_601_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_608_);
                    lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_612_);
                    v___x_614_ = v_reuseFailAlloc_618_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_597_ == 0 {
                    lean_ctor_set(v___x_596_, 0, v___x_614_);
                    v___x_616_ = v___x_596_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
                    v___x_616_ = v_reuseFailAlloc_617_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_616_;
            }
            7 => {
                v___x_627_ = lean_box(0);
                if v_isShared_626_ == 0 {
                    lean_ctor_set(v___x_625_, 0, v___x_627_);
                    v___x_629_ = v___x_625_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
                    lean_ctor_set(v_reuseFailAlloc_633_, 1, v_snd_623_);
                    v___x_629_ = v_reuseFailAlloc_633_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_597_ == 0 {
                    lean_ctor_set(v___x_596_, 0, v___x_629_);
                    v___x_631_ = v___x_596_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
                    v___x_631_ = v_reuseFailAlloc_632_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_631_;
            }
            10 => {
                if v_isShared_640_ == 0 {
                    v___x_642_ = v___x_639_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_642_;
            }
            12 => {
                v___x_648_ = lean_box(0);
                v___x_649_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_649_, 0, v___x_648_);
                lean_ctor_set(v___x_649_, 1, v_a_585_);
                if v_isShared_647_ == 0 {
                    lean_ctor_set_tag(v___x_646_, 0);
                    lean_ctor_set(v___x_646_, 0, v___x_649_);
                    v___x_651_ = v___x_646_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
                    v___x_651_ = v_reuseFailAlloc_652_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Sorry_visitDecl___boxed(
    mut v_d_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_663_: *mut LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lean_IR_Sorry_visitDecl(v_d_658_, v_a_659_, v_a_660_, v_a_661_);
    lean_dec(v_a_661_);
    lean_dec_ref(v_a_660_);
    return v_res_663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(
    mut v_as_664_: *mut LeanObject,
    mut v_i_665_: usize,
    mut v_stop_666_: usize,
    mut v_b_667_: *mut LeanObject,
    mut v___y_668_: *mut LeanObject,
    mut v___y_669_: *mut LeanObject,
    mut v___y_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: usize = 0;
    let mut v___x_679_: usize = 0;
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_672_ = lean_usize_dec_eq(v_i_665_, v_stop_666_);
                if v___x_672_ == 0 {
                    v___x_673_ = lean_array_uget_borrowed(v_as_664_, v_i_665_);
                    lean_inc(v___x_673_);
                    v___x_674_ =
                        l_Lean_IR_Sorry_visitDecl(v___x_673_, v___y_668_, v___y_669_, v___y_670_);
                    if lean_obj_tag(v___x_674_) == 0 {
                        v_a_675_ = lean_ctor_get(v___x_674_, 0);
                        lean_inc(v_a_675_);
                        lean_dec_ref_known(v___x_674_, 1);
                        v_fst_676_ = lean_ctor_get(v_a_675_, 0);
                        lean_inc(v_fst_676_);
                        v_snd_677_ = lean_ctor_get(v_a_675_, 1);
                        lean_inc(v_snd_677_);
                        lean_dec(v_a_675_);
                        v___x_678_ = 1usize;
                        v___x_679_ = lean_usize_add(v_i_665_, v___x_678_);
                        v_i_665_ = v___x_679_;
                        v_b_667_ = v_fst_676_;
                        v___y_668_ = v_snd_677_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_674_;
                    }
                } else {
                    v___x_681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_681_, 0, v_b_667_);
                    lean_ctor_set(v___x_681_, 1, v___y_668_);
                    v___x_682_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_682_, 0, v___x_681_);
                    return v___x_682_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(
    mut v_as_683_: *mut LeanObject,
    mut v_i_684_: *mut LeanObject,
    mut v_stop_685_: *mut LeanObject,
    mut v_b_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_691_: usize = 0;
    let mut v_stop_boxed_692_: usize = 0;
    let mut v_res_693_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_691_ = lean_unbox_usize(v_i_684_);
    lean_dec(v_i_684_);
    v_stop_boxed_692_ = lean_unbox_usize(v_stop_685_);
    lean_dec(v_stop_685_);
    v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_683_, v_i_boxed_691_, v_stop_boxed_692_, v_b_686_, v___y_687_, v___y_688_, v___y_689_);
    lean_dec(v___y_689_);
    lean_dec_ref(v___y_688_);
    lean_dec_ref(v_as_683_);
    return v_res_693_;
}
pub unsafe fn l_Lean_IR_Sorry_collect(
    mut v_decls_694_: *mut LeanObject,
    mut v_a_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modified_708_: u8 = 0;
    let mut v_localSorryMap_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_713_: u8 = 0;
    let mut v___x_714_: u8 = 0;
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: usize = 0;
    let mut v___x_723_: usize = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: usize = 0;
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_localSorryMap_710_ = lean_ctor_get(v_a_695_, 0);
                v_isSharedCheck_729_ = (!lean_is_exclusive(v_a_695_)) as u8;
                if v_isSharedCheck_729_ == 0 {
                    v___x_712_ = v_a_695_;
                    v_isShared_713_ = v_isSharedCheck_729_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_localSorryMap_710_);
                    lean_dec(v_a_695_);
                    v___x_712_ = lean_box(0);
                    v_isShared_713_ = v_isSharedCheck_729_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_701_ = lean_box(0);
                v___x_702_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_702_, 0, v___x_701_);
                lean_ctor_set(v___x_702_, 1, v_snd_700_);
                v___x_703_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_703_, 0, v___x_702_);
                return v___x_703_;
            }
            2 => {
                if lean_obj_tag(v___y_705_) == 0 {
                    v_a_706_ = lean_ctor_get(v___y_705_, 0);
                    lean_inc(v_a_706_);
                    lean_dec_ref_known(v___y_705_, 1);
                    v_snd_707_ = lean_ctor_get(v_a_706_, 1);
                    lean_inc(v_snd_707_);
                    lean_dec(v_a_706_);
                    v_modified_708_ = lean_ctor_get_uint8(
                        v_snd_707_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_modified_708_ == 0 {
                        v_snd_700_ = v_snd_707_;
                        state = 1;
                        continue;
                    } else {
                        v_a_695_ = v_snd_707_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v___y_705_;
                }
            }
            3 => {
                v___x_714_ = 0;
                if v_isShared_713_ == 0 {
                    v___x_716_ = v___x_712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_728_, 0, v_localSorryMap_710_);
                    v___x_716_ = v_reuseFailAlloc_728_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_ctor_set_uint8(
                    v___x_716_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_714_,
                );
                v___x_717_ = lean_unsigned_to_nat(0);
                v___x_718_ = lean_array_get_size(v_decls_694_);
                v___x_719_ = lean_nat_dec_lt(v___x_717_, v___x_718_);
                if v___x_719_ == 0 {
                    v_snd_700_ = v___x_716_;
                    state = 1;
                    continue;
                } else {
                    v___x_720_ = lean_box(0);
                    v___x_721_ = lean_nat_dec_le(v___x_718_, v___x_718_);
                    if v___x_721_ == 0 {
                        if v___x_719_ == 0 {
                            v_snd_700_ = v___x_716_;
                            state = 1;
                            continue;
                        } else {
                            v___x_722_ = 0usize;
                            v___x_723_ = lean_usize_of_nat(v___x_718_);
                            v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_694_, v___x_722_, v___x_723_, v___x_720_, v___x_716_, v_a_696_, v_a_697_);
                            v___y_705_ = v___x_724_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_725_ = 0usize;
                        v___x_726_ = lean_usize_of_nat(v___x_718_);
                        v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_decls_694_, v___x_725_, v___x_726_, v___x_720_, v___x_716_, v_a_696_, v_a_697_);
                        v___y_705_ = v___x_727_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Sorry_collect___boxed(
    mut v_decls_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_735_: *mut LeanObject = core::ptr::null_mut();
    v_res_735_ = l_Lean_IR_Sorry_collect(v_decls_730_, v_a_731_, v_a_732_, v_a_733_);
    lean_dec(v_a_733_);
    lean_dec_ref(v_a_732_);
    lean_dec_ref(v_decls_730_);
    return v_res_735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(
    mut v_snd_736_: *mut LeanObject,
    mut v_sz_737_: usize,
    mut v_i_738_: usize,
    mut v_bs_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_740_: u8 = 0;
    let mut v_v_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: usize = 0;
    let mut v___x_747_: usize = 0;
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut v_unused_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_767_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_740_ = lean_usize_dec_lt(v_i_738_, v_sz_737_);
                if v___x_740_ == 0 {
                    return v_bs_739_;
                } else {
                    v_v_741_ = lean_array_uget(v_bs_739_, v_i_738_);
                    v___x_742_ = lean_unsigned_to_nat(0);
                    v_bs_x27_743_ = lean_array_uset(v_bs_739_, v_i_738_, v___x_742_);
                    if lean_obj_tag(v_v_741_) == 0 {
                        v_f_750_ = lean_ctor_get(v_v_741_, 0);
                        v_xs_751_ = lean_ctor_get(v_v_741_, 1);
                        v_type_752_ = lean_ctor_get(v_v_741_, 2);
                        v_body_753_ = lean_ctor_get(v_v_741_, 3);
                        v_localSorryMap_754_ = lean_ctor_get(v_snd_736_, 0);
                        v___x_755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_754_, v_f_750_);
                        if lean_obj_tag(v___x_755_) == 1 {
                            lean_inc(v_body_753_);
                            lean_inc(v_type_752_);
                            lean_inc_ref(v_xs_751_);
                            lean_inc(v_f_750_);
                            v_isSharedCheck_762_ = (!lean_is_exclusive(v_v_741_)) as u8;
                            if v_isSharedCheck_762_ == 0 {
                                v_unused_763_ = lean_ctor_get(v_v_741_, 4);
                                lean_dec(v_unused_763_);
                                v_unused_764_ = lean_ctor_get(v_v_741_, 3);
                                lean_dec(v_unused_764_);
                                v_unused_765_ = lean_ctor_get(v_v_741_, 2);
                                lean_dec(v_unused_765_);
                                v_unused_766_ = lean_ctor_get(v_v_741_, 1);
                                lean_dec(v_unused_766_);
                                v_unused_767_ = lean_ctor_get(v_v_741_, 0);
                                lean_dec(v_unused_767_);
                                v___x_757_ = v_v_741_;
                                v_isShared_758_ = v_isSharedCheck_762_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_v_741_);
                                v___x_757_ = lean_box(0);
                                v_isShared_758_ = v_isSharedCheck_762_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_755_);
                            v___y_745_ = v_v_741_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_745_ = v_v_741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_746_ = 1usize;
                v___x_747_ = lean_usize_add(v_i_738_, v___x_746_);
                v___x_748_ = lean_array_uset(v_bs_x27_743_, v_i_738_, v___y_745_);
                v_i_738_ = v___x_747_;
                v_bs_739_ = v___x_748_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_758_ == 0 {
                    lean_ctor_set(v___x_757_, 4, v___x_755_);
                    v___x_760_ = v___x_757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_761_, 0, v_f_750_);
                    lean_ctor_set(v_reuseFailAlloc_761_, 1, v_xs_751_);
                    lean_ctor_set(v_reuseFailAlloc_761_, 2, v_type_752_);
                    lean_ctor_set(v_reuseFailAlloc_761_, 3, v_body_753_);
                    lean_ctor_set(v_reuseFailAlloc_761_, 4, v___x_755_);
                    v___x_760_ = v_reuseFailAlloc_761_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_745_ = v___x_760_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0___boxed(
    mut v_snd_768_: *mut LeanObject,
    mut v_sz_769_: *mut LeanObject,
    mut v_i_770_: *mut LeanObject,
    mut v_bs_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_772_: usize = 0;
    let mut v_i_boxed_773_: usize = 0;
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_772_ = lean_unbox_usize(v_sz_769_);
    lean_dec(v_sz_769_);
    v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
    lean_dec(v_i_770_);
    v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_768_, v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
    lean_dec_ref(v_snd_768_);
    return v_res_774_;
}
pub unsafe fn l_Lean_IR_updateSorryDep(
    mut v_decls_778_: *mut LeanObject,
    mut v_a_779_: *mut LeanObject,
    mut v_a_780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v_snd_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_789_: usize = 0;
    let mut v___x_790_: usize = 0;
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_795_: u8 = 0;
    let mut v_a_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_782_ = l_Lean_IR_updateSorryDep___closed__0;
                v___x_783_ = l_Lean_IR_Sorry_collect(v_decls_778_, v___x_782_, v_a_779_, v_a_780_);
                if lean_obj_tag(v___x_783_) == 0 {
                    v_a_784_ = lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_795_ = (!lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_795_ == 0 {
                        v___x_786_ = v___x_783_;
                        v_isShared_787_ = v_isSharedCheck_795_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_784_);
                        lean_dec(v___x_783_);
                        v___x_786_ = lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_795_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decls_778_);
                    v_a_796_ = lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_803_ = (!lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v___x_783_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_796_);
                        lean_dec(v___x_783_);
                        v___x_798_ = lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_788_ = lean_ctor_get(v_a_784_, 1);
                lean_inc(v_snd_788_);
                lean_dec(v_a_784_);
                v_sz_789_ = lean_array_size(v_decls_778_);
                v___x_790_ = 0usize;
                v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_788_, v_sz_789_, v___x_790_, v_decls_778_);
                lean_dec(v_snd_788_);
                if v_isShared_787_ == 0 {
                    lean_ctor_set(v___x_786_, 0, v___x_791_);
                    v___x_793_ = v___x_786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
                    v___x_793_ = v_reuseFailAlloc_794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_793_;
            }
            3 => {
                if v_isShared_799_ == 0 {
                    v___x_801_ = v___x_798_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_updateSorryDep___boxed(
    mut v_decls_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_IR_updateSorryDep(v_decls_804_, v_a_805_, v_a_806_);
    lean_dec(v_a_806_);
    lean_dec_ref(v_a_805_);
    return v_res_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Sorry(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Sorry(builtin);
}
