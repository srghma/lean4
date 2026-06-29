// Lean compiler output
// Module: Lean.Compiler.IR.Sorry
// Imports: Lean.Compiler.IR.CompilerM
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
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 111, 114, 114, 121, 65, 120, 0]};
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,5207765522374246084 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_updateSorryDep___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_updateSorryDep___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_updateSorryDep___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
    mut v_f_410_: *mut crate::leanh::LeanObject,
    mut v_a_411_: *mut crate::leanh::LeanObject,
    mut v_a_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_g_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: u8 = 0;
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    let mut v_localSorryMap_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___y_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_445_: u8 = 0;
    let mut v_a_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_453_: u8 = 0;
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_425_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
                v___x_426_ = lean_name_eq(v_f_410_, v___x_425_);
                if v___x_426_ == 0 {
                    v_localSorryMap_427_ = crate::leanh::lean_ctor_get(v_a_411_, 0);
                    v___x_428_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_427_, v_f_410_);
                    if crate::leanh::lean_obj_tag(v___x_428_) == 1 {
                        v_val_429_ = crate::leanh::lean_ctor_get(v___x_428_, 0);
                        crate::leanh::lean_inc(v_val_429_);
                        crate::leanh::lean_dec_ref_known(v___x_428_, 1);
                        v_g_415_ = v_val_429_;
                        v___y_416_ = v_a_411_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_428_);
                        crate::leanh::lean_inc(v_f_410_);
                        v___x_430_ = l_Lean_IR_findDecl___redArg(v_f_410_, v_a_412_);
                        if crate::leanh::lean_obj_tag(v___x_430_) == 0 {
                            v_a_431_ = crate::leanh::lean_ctor_get(v___x_430_, 0);
                            v_isSharedCheck_445_ =
                                (!crate::leanh::lean_is_exclusive(v___x_430_)) as u8;
                            if v_isSharedCheck_445_ == 0 {
                                v___x_433_ = v___x_430_;
                                v_isShared_434_ = v_isSharedCheck_445_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_431_);
                                crate::leanh::lean_dec(v___x_430_);
                                v___x_433_ = crate::leanh::lean_box(0);
                                v_isShared_434_ = v_isSharedCheck_445_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_a_411_);
                            crate::leanh::lean_dec(v_f_410_);
                            v_a_446_ = crate::leanh::lean_ctor_get(v___x_430_, 0);
                            v_isSharedCheck_453_ =
                                (!crate::leanh::lean_is_exclusive(v___x_430_)) as u8;
                            if v_isSharedCheck_453_ == 0 {
                                v___x_448_ = v___x_430_;
                                v_isShared_449_ = v_isSharedCheck_453_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_446_);
                                crate::leanh::lean_dec(v___x_430_);
                                v___x_448_ = crate::leanh::lean_box(0);
                                v_isShared_449_ = v_isSharedCheck_453_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_454_, 0, v_f_410_);
                    v___x_455_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
                    crate::leanh::lean_ctor_set(v___x_455_, 1, v_a_411_);
                    v___x_456_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_456_, 0, v___x_455_);
                    return v___x_456_;
                }
            }
            1 => {
                v___x_417_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__1;
                v___x_418_ = lean_name_eq(v_g_415_, v___x_417_);
                if v___x_418_ == 0 {
                    crate::leanh::lean_dec(v_f_410_);
                    v___x_419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_419_, 0, v_g_415_);
                    v___x_420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_420_, 0, v___x_419_);
                    crate::leanh::lean_ctor_set(v___x_420_, 1, v___y_416_);
                    v___x_421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_421_, 0, v___x_420_);
                    return v___x_421_;
                } else {
                    crate::leanh::lean_dec(v_g_415_);
                    v___x_422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_422_, 0, v_f_410_);
                    v___x_423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_422_);
                    crate::leanh::lean_ctor_set(v___x_423_, 1, v___y_416_);
                    v___x_424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_424_, 0, v___x_423_);
                    return v___x_424_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_431_) == 1 {
                    v_val_442_ = crate::leanh::lean_ctor_get(v_a_431_, 0);
                    crate::leanh::lean_inc(v_val_442_);
                    crate::leanh::lean_dec_ref_known(v_a_431_, 1);
                    if crate::leanh::lean_obj_tag(v_val_442_) == 0 {
                        v_info_443_ = crate::leanh::lean_ctor_get(v_val_442_, 4);
                        crate::leanh::lean_inc(v_info_443_);
                        crate::leanh::lean_dec_ref_known(v_val_442_, 5);
                        if crate::leanh::lean_obj_tag(v_info_443_) == 1 {
                            crate::leanh::lean_del_object(v___x_433_);
                            v_val_444_ = crate::leanh::lean_ctor_get(v_info_443_, 0);
                            crate::leanh::lean_inc(v_val_444_);
                            crate::leanh::lean_dec_ref_known(v_info_443_, 1);
                            v_g_415_ = v_val_444_;
                            v___y_416_ = v_a_411_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_info_443_);
                            crate::leanh::lean_dec(v_f_410_);
                            v___y_436_ = v_a_411_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_442_);
                        crate::leanh::lean_dec(v_f_410_);
                        v___y_436_ = v_a_411_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_431_);
                    crate::leanh::lean_dec(v_f_410_);
                    v___y_436_ = v_a_411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_437_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                v___x_438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_438_, 0, v___x_437_);
                crate::leanh::lean_ctor_set(v___x_438_, 1, v___y_436_);
                if v_isShared_434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_433_, 0, v___x_438_);
                    v___x_440_ = v___x_433_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
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
                    v_reuseFailAlloc_452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
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
    mut v_f_457_: *mut crate::leanh::LeanObject,
    mut v_a_458_: *mut crate::leanh::LeanObject,
    mut v_a_459_: *mut crate::leanh::LeanObject,
    mut v_a_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_461_ =
        l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
            v_f_457_, v_a_458_, v_a_459_,
        );
    crate::leanh::lean_dec(v_a_459_);
    return v_res_461_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(
    mut v_f_462_: *mut crate::leanh::LeanObject,
    mut v_a_463_: *mut crate::leanh::LeanObject,
    mut v_a_464_: *mut crate::leanh::LeanObject,
    mut v_a_465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ =
        l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(
            v_f_462_, v_a_463_, v_a_465_,
        );
    return v___x_467_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___boxed(
    mut v_f_468_: *mut crate::leanh::LeanObject,
    mut v_a_469_: *mut crate::leanh::LeanObject,
    mut v_a_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
    mut v_a_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_473_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f(
        v_f_468_, v_a_469_, v_a_470_, v_a_471_,
    );
    crate::leanh::lean_dec(v_a_471_);
    crate::leanh::lean_dec_ref(v_a_470_);
    return v_res_473_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___redArg(
    mut v_x_474_: *mut crate::leanh::LeanObject,
    mut v_a_475_: *mut crate::leanh::LeanObject,
    mut v_a_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_474_) {
        6 => {
            let mut v_c_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_478_ = crate::leanh::lean_ctor_get(v_x_474_, 0);
            crate::leanh::lean_inc(v_c_478_);
            crate::leanh::lean_dec_ref_known(v_x_474_, 2);
            v___x_479_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_478_, v_a_475_, v_a_476_);
            return v___x_479_;
        }
        7 => {
            let mut v_c_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_480_ = crate::leanh::lean_ctor_get(v_x_474_, 0);
            crate::leanh::lean_inc(v_c_480_);
            crate::leanh::lean_dec_ref_known(v_x_474_, 2);
            v___x_481_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg(v_c_480_, v_a_475_, v_a_476_);
            return v___x_481_;
        }
        _ => {
            let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_x_474_);
            v___x_482_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
            v___x_483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_483_, 0, v___x_482_);
            crate::leanh::lean_ctor_set(v___x_483_, 1, v_a_475_);
            v___x_484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_484_, 0, v___x_483_);
            return v___x_484_;
        }
    }
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___redArg___boxed(
    mut v_x_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_489_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_485_, v_a_486_, v_a_487_);
    crate::leanh::lean_dec(v_a_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr(
    mut v_x_490_: *mut crate::leanh::LeanObject,
    mut v_a_491_: *mut crate::leanh::LeanObject,
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_495_ = l_Lean_IR_Sorry_visitExpr___redArg(v_x_490_, v_a_491_, v_a_493_);
    return v___x_495_;
}
pub unsafe fn l_Lean_IR_Sorry_visitExpr___boxed(
    mut v_x_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
    mut v_a_498_: *mut crate::leanh::LeanObject,
    mut v_a_499_: *mut crate::leanh::LeanObject,
    mut v_a_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_501_ = l_Lean_IR_Sorry_visitExpr(v_x_496_, v_a_497_, v_a_498_, v_a_499_);
    crate::leanh::lean_dec(v_a_499_);
    crate::leanh::lean_dec_ref(v_a_498_);
    return v_res_501_;
}
pub unsafe fn l_Lean_IR_Sorry_visitFnBody(
    mut v_b_502_: *mut crate::leanh::LeanObject,
    mut v_a_503_: *mut crate::leanh::LeanObject,
    mut v_a_504_: *mut crate::leanh::LeanObject,
    mut v_a_505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u8 = 0;
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: usize = 0;
    let mut v___x_534_: usize = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: usize = 0;
    let mut v___x_537_: usize = 0;
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_b_502_) {
                0 => {
                    v_e_507_ = crate::leanh::lean_ctor_get(v_b_502_, 2);
                    crate::leanh::lean_inc_ref(v_e_507_);
                    v_b_508_ = crate::leanh::lean_ctor_get(v_b_502_, 3);
                    crate::leanh::lean_inc(v_b_508_);
                    crate::leanh::lean_dec_ref_known(v_b_502_, 4);
                    v___x_509_ = l_Lean_IR_Sorry_visitExpr___redArg(v_e_507_, v_a_503_, v_a_505_);
                    if crate::leanh::lean_obj_tag(v___x_509_) == 0 {
                        v_a_510_ = crate::leanh::lean_ctor_get(v___x_509_, 0);
                        crate::leanh::lean_inc(v_a_510_);
                        v_fst_511_ = crate::leanh::lean_ctor_get(v_a_510_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_511_) == 0 {
                            crate::leanh::lean_dec(v_a_510_);
                            crate::leanh::lean_dec(v_b_508_);
                            return v___x_509_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_509_, 1);
                            v_snd_512_ = crate::leanh::lean_ctor_get(v_a_510_, 1);
                            crate::leanh::lean_inc(v_snd_512_);
                            crate::leanh::lean_dec(v_a_510_);
                            v_b_502_ = v_b_508_;
                            v_a_503_ = v_snd_512_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_508_);
                        return v___x_509_;
                    }
                }
                1 => {
                    v_v_514_ = crate::leanh::lean_ctor_get(v_b_502_, 2);
                    crate::leanh::lean_inc(v_v_514_);
                    v_b_515_ = crate::leanh::lean_ctor_get(v_b_502_, 3);
                    crate::leanh::lean_inc(v_b_515_);
                    crate::leanh::lean_dec_ref_known(v_b_502_, 4);
                    v___x_516_ =
                        l_Lean_IR_Sorry_visitFnBody(v_v_514_, v_a_503_, v_a_504_, v_a_505_);
                    if crate::leanh::lean_obj_tag(v___x_516_) == 0 {
                        v_a_517_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
                        crate::leanh::lean_inc(v_a_517_);
                        v_fst_518_ = crate::leanh::lean_ctor_get(v_a_517_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_518_) == 0 {
                            crate::leanh::lean_dec(v_a_517_);
                            crate::leanh::lean_dec(v_b_515_);
                            return v___x_516_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_516_, 1);
                            v_snd_519_ = crate::leanh::lean_ctor_get(v_a_517_, 1);
                            crate::leanh::lean_inc(v_snd_519_);
                            crate::leanh::lean_dec(v_a_517_);
                            v_b_502_ = v_b_515_;
                            v_a_503_ = v_snd_519_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_b_515_);
                        return v___x_516_;
                    }
                }
                9 => {
                    v_cs_521_ = crate::leanh::lean_ctor_get(v_b_502_, 3);
                    crate::leanh::lean_inc_ref(v_cs_521_);
                    crate::leanh::lean_dec_ref_known(v_b_502_, 4);
                    v___x_522_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_523_ = lean_array_get_size(v_cs_521_);
                    v___x_524_ = crate::leanh::lean_box(0);
                    v___x_525_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
                    if v___x_525_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_521_);
                        v___x_526_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                        v___x_527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_527_, 0, v___x_526_);
                        crate::leanh::lean_ctor_set(v___x_527_, 1, v_a_503_);
                        v___x_528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_528_, 0, v___x_527_);
                        return v___x_528_;
                    } else {
                        v___x_529_ = lean_nat_dec_le(v___x_523_, v___x_523_);
                        if v___x_529_ == 0 {
                            if v___x_525_ == 0 {
                                crate::leanh::lean_dec_ref(v_cs_521_);
                                v___x_530_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                                v___x_531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_531_, 0, v___x_530_);
                                crate::leanh::lean_ctor_set(v___x_531_, 1, v_a_503_);
                                v___x_532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_532_, 0, v___x_531_);
                                return v___x_532_;
                            } else {
                                v___x_533_ = 0usize;
                                v___x_534_ = lean_usize_of_nat(v___x_523_);
                                v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_521_, v___x_533_, v___x_534_, v___x_524_, v_a_503_, v_a_504_, v_a_505_);
                                crate::leanh::lean_dec_ref(v_cs_521_);
                                return v___x_535_;
                            }
                        } else {
                            v___x_536_ = 0usize;
                            v___x_537_ = lean_usize_of_nat(v___x_523_);
                            v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_cs_521_, v___x_536_, v___x_537_, v___x_524_, v_a_503_, v_a_504_, v_a_505_);
                            crate::leanh::lean_dec_ref(v_cs_521_);
                            return v___x_538_;
                        }
                    }
                }
                _ => {
                    v___x_539_ = l_Lean_IR_FnBody_isTerminal(v_b_502_);
                    if v___x_539_ == 0 {
                        v___x_540_ = l_Lean_IR_FnBody_body(v_b_502_);
                        crate::leanh::lean_dec(v_b_502_);
                        v_b_502_ = v___x_540_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_502_);
                        v___x_542_ = l___private_Lean_Compiler_IR_Sorry_0__Lean_IR_Sorry_visitExpr_getSorryDepFor_x3f___redArg___closed__2;
                        v___x_543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_542_);
                        crate::leanh::lean_ctor_set(v___x_543_, 1, v_a_503_);
                        v___x_544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_544_, 0, v___x_543_);
                        return v___x_544_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(
    mut v_as_545_: *mut crate::leanh::LeanObject,
    mut v_i_546_: usize,
    mut v_stop_547_: usize,
    mut v_b_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
    mut v___y_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553_: u8 = 0;
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: usize = 0;
    let mut v___x_562_: usize = 0;
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    if crate::leanh::lean_obj_tag(v___x_556_) == 0 {
                        v_a_557_ = crate::leanh::lean_ctor_get(v___x_556_, 0);
                        crate::leanh::lean_inc(v_a_557_);
                        v_fst_558_ = crate::leanh::lean_ctor_get(v_a_557_, 0);
                        crate::leanh::lean_inc(v_fst_558_);
                        if crate::leanh::lean_obj_tag(v_fst_558_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_fst_558_, 1);
                            crate::leanh::lean_dec(v_a_557_);
                            return v___x_556_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_556_, 1);
                            v_snd_559_ = crate::leanh::lean_ctor_get(v_a_557_, 1);
                            crate::leanh::lean_inc(v_snd_559_);
                            crate::leanh::lean_dec(v_a_557_);
                            v_a_560_ = crate::leanh::lean_ctor_get(v_fst_558_, 0);
                            crate::leanh::lean_inc(v_a_560_);
                            crate::leanh::lean_dec_ref_known(v_fst_558_, 1);
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
                    v___x_564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_564_, 0, v_b_548_);
                    v___x_565_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_565_, 0, v___x_564_);
                    crate::leanh::lean_ctor_set(v___x_565_, 1, v___y_549_);
                    v___x_566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_566_, 0, v___x_565_);
                    return v___x_566_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0___boxed(
    mut v_as_567_: *mut crate::leanh::LeanObject,
    mut v_i_568_: *mut crate::leanh::LeanObject,
    mut v_stop_569_: *mut crate::leanh::LeanObject,
    mut v_b_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
    mut v___y_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_575_: usize = 0;
    let mut v_stop_boxed_576_: usize = 0;
    let mut v_res_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_575_ = crate::leanh::lean_unbox_usize(v_i_568_);
    crate::leanh::lean_dec(v_i_568_);
    v_stop_boxed_576_ = crate::leanh::lean_unbox_usize(v_stop_569_);
    crate::leanh::lean_dec(v_stop_569_);
    v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_visitFnBody_spec__0(v_as_567_, v_i_boxed_575_, v_stop_boxed_576_, v_b_570_, v___y_571_, v___y_572_, v___y_573_);
    crate::leanh::lean_dec(v___y_573_);
    crate::leanh::lean_dec_ref(v___y_572_);
    crate::leanh::lean_dec_ref(v_as_567_);
    return v_res_577_;
}
pub unsafe fn l_Lean_IR_Sorry_visitFnBody___boxed(
    mut v_b_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
    mut v_a_580_: *mut crate::leanh::LeanObject,
    mut v_a_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_583_ = l_Lean_IR_Sorry_visitFnBody(v_b_578_, v_a_579_, v_a_580_, v_a_581_);
    crate::leanh::lean_dec(v_a_581_);
    crate::leanh::lean_dec_ref(v_a_580_);
    return v_res_583_;
}
pub unsafe fn l_Lean_IR_Sorry_visitDecl(
    mut v_d_584_: *mut crate::leanh::LeanObject,
    mut v_a_585_: *mut crate::leanh::LeanObject,
    mut v_a_586_: *mut crate::leanh::LeanObject,
    mut v_a_587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_597_: u8 = 0;
    let mut v_fst_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v_a_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut v_unused_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_634_: u8 = 0;
    let mut v_unused_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_636_: u8 = 0;
    let mut v_a_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut v_unused_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_d_584_) == 0 {
                    v_f_589_ = crate::leanh::lean_ctor_get(v_d_584_, 0);
                    crate::leanh::lean_inc(v_f_589_);
                    v_body_590_ = crate::leanh::lean_ctor_get(v_d_584_, 3);
                    crate::leanh::lean_inc(v_body_590_);
                    crate::leanh::lean_dec_ref_known(v_d_584_, 5);
                    v_localSorryMap_591_ = crate::leanh::lean_ctor_get(v_a_585_, 0);
                    v___x_592_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_591_, v_f_589_);
                    if crate::leanh::lean_obj_tag(v___x_592_) == 0 {
                        v___x_593_ =
                            l_Lean_IR_Sorry_visitFnBody(v_body_590_, v_a_585_, v_a_586_, v_a_587_);
                        if crate::leanh::lean_obj_tag(v___x_593_) == 0 {
                            v_a_594_ = crate::leanh::lean_ctor_get(v___x_593_, 0);
                            v_isSharedCheck_636_ =
                                (!crate::leanh::lean_is_exclusive(v___x_593_)) as u8;
                            if v_isSharedCheck_636_ == 0 {
                                v___x_596_ = v___x_593_;
                                v_isShared_597_ = v_isSharedCheck_636_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_594_);
                                crate::leanh::lean_dec(v___x_593_);
                                v___x_596_ = crate::leanh::lean_box(0);
                                v_isShared_597_ = v_isSharedCheck_636_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_f_589_);
                            v_a_637_ = crate::leanh::lean_ctor_get(v___x_593_, 0);
                            v_isSharedCheck_644_ =
                                (!crate::leanh::lean_is_exclusive(v___x_593_)) as u8;
                            if v_isSharedCheck_644_ == 0 {
                                v___x_639_ = v___x_593_;
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_637_);
                                crate::leanh::lean_dec(v___x_593_);
                                v___x_639_ = crate::leanh::lean_box(0);
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_body_590_);
                        crate::leanh::lean_dec(v_f_589_);
                        v_isSharedCheck_653_ = (!crate::leanh::lean_is_exclusive(v___x_592_)) as u8;
                        if v_isSharedCheck_653_ == 0 {
                            v_unused_654_ = crate::leanh::lean_ctor_get(v___x_592_, 0);
                            crate::leanh::lean_dec(v_unused_654_);
                            v___x_646_ = v___x_592_;
                            v_isShared_647_ = v_isSharedCheck_653_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_592_);
                            v___x_646_ = crate::leanh::lean_box(0);
                            v_isShared_647_ = v_isSharedCheck_653_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_d_584_);
                    v___x_655_ = crate::leanh::lean_box(0);
                    v___x_656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_656_, 0, v___x_655_);
                    crate::leanh::lean_ctor_set(v___x_656_, 1, v_a_585_);
                    v___x_657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_656_);
                    return v___x_657_;
                }
            }
            1 => {
                v_fst_598_ = crate::leanh::lean_ctor_get(v_a_594_, 0);
                if crate::leanh::lean_obj_tag(v_fst_598_) == 0 {
                    crate::leanh::lean_inc_ref(v_fst_598_);
                    v_snd_599_ = crate::leanh::lean_ctor_get(v_a_594_, 1);
                    v_isSharedCheck_621_ = (!crate::leanh::lean_is_exclusive(v_a_594_)) as u8;
                    if v_isSharedCheck_621_ == 0 {
                        v_unused_622_ = crate::leanh::lean_ctor_get(v_a_594_, 0);
                        crate::leanh::lean_dec(v_unused_622_);
                        v___x_601_ = v_a_594_;
                        v_isShared_602_ = v_isSharedCheck_621_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_599_);
                        crate::leanh::lean_dec(v_a_594_);
                        v___x_601_ = crate::leanh::lean_box(0);
                        v_isShared_602_ = v_isSharedCheck_621_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_589_);
                    v_snd_623_ = crate::leanh::lean_ctor_get(v_a_594_, 1);
                    v_isSharedCheck_634_ = (!crate::leanh::lean_is_exclusive(v_a_594_)) as u8;
                    if v_isSharedCheck_634_ == 0 {
                        v_unused_635_ = crate::leanh::lean_ctor_get(v_a_594_, 0);
                        crate::leanh::lean_dec(v_unused_635_);
                        v___x_625_ = v_a_594_;
                        v_isShared_626_ = v_isSharedCheck_634_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_623_);
                        crate::leanh::lean_dec(v_a_594_);
                        v___x_625_ = crate::leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_634_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_a_603_ = crate::leanh::lean_ctor_get(v_fst_598_, 0);
                crate::leanh::lean_inc(v_a_603_);
                crate::leanh::lean_dec_ref_known(v_fst_598_, 1);
                v_localSorryMap_604_ = crate::leanh::lean_ctor_get(v_snd_599_, 0);
                v_isSharedCheck_620_ = (!crate::leanh::lean_is_exclusive(v_snd_599_)) as u8;
                if v_isSharedCheck_620_ == 0 {
                    v___x_606_ = v_snd_599_;
                    v_isShared_607_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_localSorryMap_604_);
                    crate::leanh::lean_dec(v_snd_599_);
                    v___x_606_ = crate::leanh::lean_box(0);
                    v_isShared_607_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_608_ = crate::leanh::lean_box(0);
                v___x_609_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_f_589_, v_a_603_, v_localSorryMap_604_);
                v___x_610_ = 1;
                if v_isShared_607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_606_, 0, v___x_609_);
                    v___x_612_ = v___x_606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_609_);
                    v___x_612_ = v_reuseFailAlloc_619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_610_,
                );
                if v_isShared_602_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_601_, 1, v___x_612_);
                    crate::leanh::lean_ctor_set(v___x_601_, 0, v___x_608_);
                    v___x_614_ = v___x_601_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_612_);
                    v___x_614_ = v_reuseFailAlloc_618_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_596_, 0, v___x_614_);
                    v___x_616_ = v___x_596_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
                    v___x_616_ = v_reuseFailAlloc_617_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_616_;
            }
            7 => {
                v___x_627_ = crate::leanh::lean_box(0);
                if v_isShared_626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_627_);
                    v___x_629_ = v___x_625_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_633_, 1, v_snd_623_);
                    v___x_629_ = v_reuseFailAlloc_633_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_597_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_596_, 0, v___x_629_);
                    v___x_631_ = v___x_596_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
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
                    v_reuseFailAlloc_643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_642_;
            }
            12 => {
                v___x_648_ = crate::leanh::lean_box(0);
                v___x_649_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_648_);
                crate::leanh::lean_ctor_set(v___x_649_, 1, v_a_585_);
                if v_isShared_647_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_646_, 0);
                    crate::leanh::lean_ctor_set(v___x_646_, 0, v___x_649_);
                    v___x_651_ = v___x_646_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
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
    mut v_d_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
    mut v_a_660_: *mut crate::leanh::LeanObject,
    mut v_a_661_: *mut crate::leanh::LeanObject,
    mut v_a_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lean_IR_Sorry_visitDecl(v_d_658_, v_a_659_, v_a_660_, v_a_661_);
    crate::leanh::lean_dec(v_a_661_);
    crate::leanh::lean_dec_ref(v_a_660_);
    return v_res_663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(
    mut v_as_664_: *mut crate::leanh::LeanObject,
    mut v_i_665_: usize,
    mut v_stop_666_: usize,
    mut v_b_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
    mut v___y_669_: *mut crate::leanh::LeanObject,
    mut v___y_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: usize = 0;
    let mut v___x_679_: usize = 0;
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_672_ = lean_usize_dec_eq(v_i_665_, v_stop_666_);
                if v___x_672_ == 0 {
                    v___x_673_ = lean_array_uget_borrowed(v_as_664_, v_i_665_);
                    crate::leanh::lean_inc(v___x_673_);
                    v___x_674_ =
                        l_Lean_IR_Sorry_visitDecl(v___x_673_, v___y_668_, v___y_669_, v___y_670_);
                    if crate::leanh::lean_obj_tag(v___x_674_) == 0 {
                        v_a_675_ = crate::leanh::lean_ctor_get(v___x_674_, 0);
                        crate::leanh::lean_inc(v_a_675_);
                        crate::leanh::lean_dec_ref_known(v___x_674_, 1);
                        v_fst_676_ = crate::leanh::lean_ctor_get(v_a_675_, 0);
                        crate::leanh::lean_inc(v_fst_676_);
                        v_snd_677_ = crate::leanh::lean_ctor_get(v_a_675_, 1);
                        crate::leanh::lean_inc(v_snd_677_);
                        crate::leanh::lean_dec(v_a_675_);
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
                    v___x_681_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_681_, 0, v_b_667_);
                    crate::leanh::lean_ctor_set(v___x_681_, 1, v___y_668_);
                    v___x_682_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_682_, 0, v___x_681_);
                    return v___x_682_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0___boxed(
    mut v_as_683_: *mut crate::leanh::LeanObject,
    mut v_i_684_: *mut crate::leanh::LeanObject,
    mut v_stop_685_: *mut crate::leanh::LeanObject,
    mut v_b_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
    mut v___y_689_: *mut crate::leanh::LeanObject,
    mut v___y_690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_691_: usize = 0;
    let mut v_stop_boxed_692_: usize = 0;
    let mut v_res_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_691_ = crate::leanh::lean_unbox_usize(v_i_684_);
    crate::leanh::lean_dec(v_i_684_);
    v_stop_boxed_692_ = crate::leanh::lean_unbox_usize(v_stop_685_);
    crate::leanh::lean_dec(v_stop_685_);
    v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_Sorry_collect_spec__0(v_as_683_, v_i_boxed_691_, v_stop_boxed_692_, v_b_686_, v___y_687_, v___y_688_, v___y_689_);
    crate::leanh::lean_dec(v___y_689_);
    crate::leanh::lean_dec_ref(v___y_688_);
    crate::leanh::lean_dec_ref(v_as_683_);
    return v_res_693_;
}
pub unsafe fn l_Lean_IR_Sorry_collect(
    mut v_decls_694_: *mut crate::leanh::LeanObject,
    mut v_a_695_: *mut crate::leanh::LeanObject,
    mut v_a_696_: *mut crate::leanh::LeanObject,
    mut v_a_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_708_: u8 = 0;
    let mut v_localSorryMap_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_713_: u8 = 0;
    let mut v___x_714_: u8 = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: u8 = 0;
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: usize = 0;
    let mut v___x_723_: usize = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: usize = 0;
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_localSorryMap_710_ = crate::leanh::lean_ctor_get(v_a_695_, 0);
                v_isSharedCheck_729_ = (!crate::leanh::lean_is_exclusive(v_a_695_)) as u8;
                if v_isSharedCheck_729_ == 0 {
                    v___x_712_ = v_a_695_;
                    v_isShared_713_ = v_isSharedCheck_729_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_localSorryMap_710_);
                    crate::leanh::lean_dec(v_a_695_);
                    v___x_712_ = crate::leanh::lean_box(0);
                    v_isShared_713_ = v_isSharedCheck_729_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_701_ = crate::leanh::lean_box(0);
                v___x_702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_701_);
                crate::leanh::lean_ctor_set(v___x_702_, 1, v_snd_700_);
                v___x_703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_702_);
                return v___x_703_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_705_) == 0 {
                    v_a_706_ = crate::leanh::lean_ctor_get(v___y_705_, 0);
                    crate::leanh::lean_inc(v_a_706_);
                    crate::leanh::lean_dec_ref_known(v___y_705_, 1);
                    v_snd_707_ = crate::leanh::lean_ctor_get(v_a_706_, 1);
                    crate::leanh::lean_inc(v_snd_707_);
                    crate::leanh::lean_dec(v_a_706_);
                    v_modified_708_ = crate::leanh::lean_ctor_get_uint8(
                        v_snd_707_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    v_reuseFailAlloc_728_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_728_, 0, v_localSorryMap_710_);
                    v___x_716_ = v_reuseFailAlloc_728_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_716_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_714_,
                );
                v___x_717_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_718_ = lean_array_get_size(v_decls_694_);
                v___x_719_ = lean_nat_dec_lt(v___x_717_, v___x_718_);
                if v___x_719_ == 0 {
                    v_snd_700_ = v___x_716_;
                    state = 1;
                    continue;
                } else {
                    v___x_720_ = crate::leanh::lean_box(0);
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
    mut v_decls_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_a_732_: *mut crate::leanh::LeanObject,
    mut v_a_733_: *mut crate::leanh::LeanObject,
    mut v_a_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_735_ = l_Lean_IR_Sorry_collect(v_decls_730_, v_a_731_, v_a_732_, v_a_733_);
    crate::leanh::lean_dec(v_a_733_);
    crate::leanh::lean_dec_ref(v_a_732_);
    crate::leanh::lean_dec_ref(v_decls_730_);
    return v_res_735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(
    mut v_snd_736_: *mut crate::leanh::LeanObject,
    mut v_sz_737_: usize,
    mut v_i_738_: usize,
    mut v_bs_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: u8 = 0;
    let mut v_v_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: usize = 0;
    let mut v___x_747_: usize = 0;
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localSorryMap_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut v_unused_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_740_ = lean_usize_dec_lt(v_i_738_, v_sz_737_);
                if v___x_740_ == 0 {
                    return v_bs_739_;
                } else {
                    v_v_741_ = lean_array_uget(v_bs_739_, v_i_738_);
                    v___x_742_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_743_ = lean_array_uset(v_bs_739_, v_i_738_, v___x_742_);
                    if crate::leanh::lean_obj_tag(v_v_741_) == 0 {
                        v_f_750_ = crate::leanh::lean_ctor_get(v_v_741_, 0);
                        v_xs_751_ = crate::leanh::lean_ctor_get(v_v_741_, 1);
                        v_type_752_ = crate::leanh::lean_ctor_get(v_v_741_, 2);
                        v_body_753_ = crate::leanh::lean_ctor_get(v_v_741_, 3);
                        v_localSorryMap_754_ = crate::leanh::lean_ctor_get(v_snd_736_, 0);
                        v___x_755_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_754_, v_f_750_);
                        if crate::leanh::lean_obj_tag(v___x_755_) == 1 {
                            crate::leanh::lean_inc(v_body_753_);
                            crate::leanh::lean_inc(v_type_752_);
                            crate::leanh::lean_inc_ref(v_xs_751_);
                            crate::leanh::lean_inc(v_f_750_);
                            v_isSharedCheck_762_ =
                                (!crate::leanh::lean_is_exclusive(v_v_741_)) as u8;
                            if v_isSharedCheck_762_ == 0 {
                                v_unused_763_ = crate::leanh::lean_ctor_get(v_v_741_, 4);
                                crate::leanh::lean_dec(v_unused_763_);
                                v_unused_764_ = crate::leanh::lean_ctor_get(v_v_741_, 3);
                                crate::leanh::lean_dec(v_unused_764_);
                                v_unused_765_ = crate::leanh::lean_ctor_get(v_v_741_, 2);
                                crate::leanh::lean_dec(v_unused_765_);
                                v_unused_766_ = crate::leanh::lean_ctor_get(v_v_741_, 1);
                                crate::leanh::lean_dec(v_unused_766_);
                                v_unused_767_ = crate::leanh::lean_ctor_get(v_v_741_, 0);
                                crate::leanh::lean_dec(v_unused_767_);
                                v___x_757_ = v_v_741_;
                                v_isShared_758_ = v_isSharedCheck_762_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_v_741_);
                                v___x_757_ = crate::leanh::lean_box(0);
                                v_isShared_758_ = v_isSharedCheck_762_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_755_);
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
                    crate::leanh::lean_ctor_set(v___x_757_, 4, v___x_755_);
                    v___x_760_ = v___x_757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_761_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 0, v_f_750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 1, v_xs_751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 2, v_type_752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 3, v_body_753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 4, v___x_755_);
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
    mut v_snd_768_: *mut crate::leanh::LeanObject,
    mut v_sz_769_: *mut crate::leanh::LeanObject,
    mut v_i_770_: *mut crate::leanh::LeanObject,
    mut v_bs_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_772_: usize = 0;
    let mut v_i_boxed_773_: usize = 0;
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_772_ = crate::leanh::lean_unbox_usize(v_sz_769_);
    crate::leanh::lean_dec(v_sz_769_);
    v_i_boxed_773_ = crate::leanh::lean_unbox_usize(v_i_770_);
    crate::leanh::lean_dec(v_i_770_);
    v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_768_, v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
    crate::leanh::lean_dec_ref(v_snd_768_);
    return v_res_774_;
}
pub unsafe fn l_Lean_IR_updateSorryDep(
    mut v_decls_778_: *mut crate::leanh::LeanObject,
    mut v_a_779_: *mut crate::leanh::LeanObject,
    mut v_a_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v_snd_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_789_: usize = 0;
    let mut v___x_790_: usize = 0;
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_795_: u8 = 0;
    let mut v_a_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_782_ = l_Lean_IR_updateSorryDep___closed__0;
                v___x_783_ = l_Lean_IR_Sorry_collect(v_decls_778_, v___x_782_, v_a_779_, v_a_780_);
                if crate::leanh::lean_obj_tag(v___x_783_) == 0 {
                    v_a_784_ = crate::leanh::lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_795_ = (!crate::leanh::lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_795_ == 0 {
                        v___x_786_ = v___x_783_;
                        v_isShared_787_ = v_isSharedCheck_795_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_784_);
                        crate::leanh::lean_dec(v___x_783_);
                        v___x_786_ = crate::leanh::lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_795_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_decls_778_);
                    v_a_796_ = crate::leanh::lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_803_ = (!crate::leanh::lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_798_ = v___x_783_;
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_796_);
                        crate::leanh::lean_dec(v___x_783_);
                        v___x_798_ = crate::leanh::lean_box(0);
                        v_isShared_799_ = v_isSharedCheck_803_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_788_ = crate::leanh::lean_ctor_get(v_a_784_, 1);
                crate::leanh::lean_inc(v_snd_788_);
                crate::leanh::lean_dec(v_a_784_);
                v_sz_789_ = lean_array_size(v_decls_778_);
                v___x_790_ = 0usize;
                v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_updateSorryDep_spec__0(v_snd_788_, v_sz_789_, v___x_790_, v_decls_778_);
                crate::leanh::lean_dec(v_snd_788_);
                if v_isShared_787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_786_, 0, v___x_791_);
                    v___x_793_ = v___x_786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
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
                    v_reuseFailAlloc_802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
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
    mut v_decls_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_IR_updateSorryDep(v_decls_804_, v_a_805_, v_a_806_);
    crate::leanh::lean_dec(v_a_806_);
    crate::leanh::lean_dec_ref(v_a_805_);
    return v_res_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Sorry(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Sorry(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Sorry(builtin);
}
