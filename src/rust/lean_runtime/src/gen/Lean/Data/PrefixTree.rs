// Lean compiler output
// Module: Lean.Data.PrefixTree
// Imports: Std.Data.TreeMap.Raw.Basic
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert_x21___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg,
    l_Std_DTreeMap_Internal_Impl_foldlM___redArg,
};
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_instInhabitedPrefixTreeNode___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedPrefixTreeNode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPrefixTreeNode___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_instInhabitedPrefixTreeNode(
    mut v_00_u03b1_408_: *mut LeanObject,
    mut v_00_u03b2_409_: *mut LeanObject,
    mut v_cmp_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_instInhabitedPrefixTreeNode___closed__0;
    return v___x_411_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTreeNode___boxed(
    mut v_00_u03b1_412_: *mut LeanObject,
    mut v_00_u03b2_413_: *mut LeanObject,
    mut v_cmp_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_415_: *mut LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Lean_instInhabitedPrefixTreeNode(v_00_u03b1_412_, v_00_u03b2_413_, v_cmp_414_);
    lean_dec_ref(v_cmp_414_);
    return v_res_415_;
}
pub unsafe fn l_Lean_PrefixTreeNode_empty(
    mut v_00_u03b1_416_: *mut LeanObject,
    mut v_00_u03b2_417_: *mut LeanObject,
    mut v_cmp_418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_instInhabitedPrefixTreeNode___closed__0;
    return v___x_419_;
}
pub unsafe fn l_Lean_PrefixTreeNode_empty___boxed(
    mut v_00_u03b1_420_: *mut LeanObject,
    mut v_00_u03b2_421_: *mut LeanObject,
    mut v_cmp_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_423_: *mut LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_PrefixTreeNode_empty(v_00_u03b1_420_, v_00_u03b2_421_, v_cmp_422_);
    lean_dec_ref(v_cmp_422_);
    return v_res_423_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(
    mut v_cmp_424_: *mut LeanObject,
    mut v_val_425_: *mut LeanObject,
    mut v_k_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v_t_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_k_426_) == 0 {
                    lean_dec_ref(v_cmp_424_);
                    v___x_427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_427_, 0, v_val_425_);
                    v___x_428_ = lean_box(1);
                    v___x_429_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_429_, 0, v___x_427_);
                    lean_ctor_set(v___x_429_, 1, v___x_428_);
                    return v___x_429_;
                } else {
                    v_head_430_ = lean_ctor_get(v_k_426_, 0);
                    v_tail_431_ = lean_ctor_get(v_k_426_, 1);
                    v_isSharedCheck_442_ = (!lean_is_exclusive(v_k_426_)) as u8;
                    if v_isSharedCheck_442_ == 0 {
                        v___x_433_ = v_k_426_;
                        v_isShared_434_ = v_isSharedCheck_442_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_431_);
                        lean_inc(v_head_430_);
                        lean_dec(v_k_426_);
                        v___x_433_ = lean_box(0);
                        v_isShared_434_ = v_isSharedCheck_442_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_cmp_424_);
                v_t_435_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_424_, v_val_425_, v_tail_431_);
                v___x_436_ = lean_box(0);
                v___x_437_ = lean_box(1);
                v___x_438_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                    v_cmp_424_,
                    v_head_430_,
                    v_t_435_,
                    v___x_437_,
                );
                if v_isShared_434_ == 0 {
                    lean_ctor_set_tag(v___x_433_, 0);
                    lean_ctor_set(v___x_433_, 1, v___x_438_);
                    lean_ctor_set(v___x_433_, 0, v___x_436_);
                    v___x_440_ = v___x_433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_436_);
                    lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty(
    mut v_00_u03b1_443_: *mut LeanObject,
    mut v_00_u03b2_444_: *mut LeanObject,
    mut v_cmp_445_: *mut LeanObject,
    mut v_val_446_: *mut LeanObject,
    mut v_k_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    v___x_448_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(
            v_cmp_445_, v_val_446_, v_k_447_,
        );
    return v___x_448_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
    mut v_cmp_449_: *mut LeanObject,
    mut v_val_450_: *mut LeanObject,
    mut v_x_451_: *mut LeanObject,
    mut v_x_452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_456_: u8 = 0;
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut v_unused_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_467_: u8 = 0;
    let mut v_head_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_452_) == 0 {
                    lean_dec_ref(v_cmp_449_);
                    v_a_453_ = lean_ctor_get(v_x_451_, 1);
                    v_isSharedCheck_461_ = (!lean_is_exclusive(v_x_451_)) as u8;
                    if v_isSharedCheck_461_ == 0 {
                        v_unused_462_ = lean_ctor_get(v_x_451_, 0);
                        lean_dec(v_unused_462_);
                        v___x_455_ = v_x_451_;
                        v_isShared_456_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_453_);
                        lean_dec(v_x_451_);
                        v___x_455_ = lean_box(0);
                        v_isShared_456_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_463_ = lean_ctor_get(v_x_451_, 0);
                    v_a_464_ = lean_ctor_get(v_x_451_, 1);
                    v_isSharedCheck_480_ = (!lean_is_exclusive(v_x_451_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_466_ = v_x_451_;
                        v_isShared_467_ = v_isSharedCheck_480_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_464_);
                        lean_inc(v_a_463_);
                        lean_dec(v_x_451_);
                        v___x_466_ = lean_box(0);
                        v_isShared_467_ = v_isSharedCheck_480_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_457_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_457_, 0, v_val_450_);
                if v_isShared_456_ == 0 {
                    lean_ctor_set(v___x_455_, 0, v___x_457_);
                    v___x_459_ = v___x_455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
                    lean_ctor_set(v_reuseFailAlloc_460_, 1, v_a_453_);
                    v___x_459_ = v_reuseFailAlloc_460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_459_;
            }
            3 => {
                v_head_468_ = lean_ctor_get(v_x_452_, 0);
                lean_inc_n(v_head_468_, 2);
                v_tail_469_ = lean_ctor_get(v_x_452_, 1);
                lean_inc(v_tail_469_);
                lean_dec_ref_known(v_x_452_, 2);
                lean_inc(v_a_464_);
                lean_inc_ref(v_cmp_449_);
                v___x_476_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                    v_cmp_449_,
                    v_a_464_,
                    v_head_468_,
                );
                if lean_obj_tag(v___x_476_) == 0 {
                    lean_inc_ref(v_cmp_449_);
                    v___x_477_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_449_, v_val_450_, v_tail_469_);
                    v___y_471_ = v___x_477_;
                    state = 4;
                    continue;
                } else {
                    v_val_478_ = lean_ctor_get(v___x_476_, 0);
                    lean_inc(v_val_478_);
                    lean_dec_ref_known(v___x_476_, 1);
                    lean_inc_ref(v_cmp_449_);
                    v___x_479_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(v_cmp_449_, v_val_450_, v_val_478_, v_tail_469_);
                    v___y_471_ = v___x_479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_472_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                    v_cmp_449_,
                    v_head_468_,
                    v___y_471_,
                    v_a_464_,
                );
                if v_isShared_467_ == 0 {
                    lean_ctor_set(v___x_466_, 1, v___x_472_);
                    v___x_474_ = v___x_466_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_463_);
                    lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
                    v___x_474_ = v_reuseFailAlloc_475_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop(
    mut v_00_u03b1_481_: *mut LeanObject,
    mut v_00_u03b2_482_: *mut LeanObject,
    mut v_cmp_483_: *mut LeanObject,
    mut v_val_484_: *mut LeanObject,
    mut v_x_485_: *mut LeanObject,
    mut v_x_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_483_, v_val_484_, v_x_485_, v_x_486_,
    );
    return v___x_487_;
}
pub unsafe fn l_Lean_PrefixTreeNode_insert___redArg(
    mut v_cmp_488_: *mut LeanObject,
    mut v_t_489_: *mut LeanObject,
    mut v_k_490_: *mut LeanObject,
    mut v_val_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_488_, v_val_491_, v_t_489_, v_k_490_,
    );
    return v___x_492_;
}
pub unsafe fn l_Lean_PrefixTreeNode_insert(
    mut v_00_u03b1_493_: *mut LeanObject,
    mut v_00_u03b2_494_: *mut LeanObject,
    mut v_cmp_495_: *mut LeanObject,
    mut v_t_496_: *mut LeanObject,
    mut v_k_497_: *mut LeanObject,
    mut v_val_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_495_, v_val_498_, v_t_496_, v_k_497_,
    );
    return v___x_499_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
    mut v_cmp_500_: *mut LeanObject,
    mut v_x_501_: *mut LeanObject,
    mut v_x_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_502_) == 0 {
                    lean_dec_ref(v_cmp_500_);
                    v_a_503_ = lean_ctor_get(v_x_501_, 0);
                    lean_inc(v_a_503_);
                    lean_dec_ref(v_x_501_);
                    return v_a_503_;
                } else {
                    v_a_504_ = lean_ctor_get(v_x_501_, 1);
                    lean_inc(v_a_504_);
                    lean_dec_ref(v_x_501_);
                    v_head_505_ = lean_ctor_get(v_x_502_, 0);
                    lean_inc(v_head_505_);
                    v_tail_506_ = lean_ctor_get(v_x_502_, 1);
                    lean_inc(v_tail_506_);
                    lean_dec_ref_known(v_x_502_, 2);
                    lean_inc_ref(v_cmp_500_);
                    v___x_507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_500_,
                        v_a_504_,
                        v_head_505_,
                    );
                    if lean_obj_tag(v___x_507_) == 0 {
                        lean_dec(v_tail_506_);
                        lean_dec_ref(v_cmp_500_);
                        v___x_508_ = lean_box(0);
                        return v___x_508_;
                    } else {
                        v_val_509_ = lean_ctor_get(v___x_507_, 0);
                        lean_inc(v_val_509_);
                        lean_dec_ref_known(v___x_507_, 1);
                        v_x_501_ = v_val_509_;
                        v_x_502_ = v_tail_506_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop(
    mut v_00_u03b1_511_: *mut LeanObject,
    mut v_00_u03b2_512_: *mut LeanObject,
    mut v_cmp_513_: *mut LeanObject,
    mut v_x_514_: *mut LeanObject,
    mut v_x_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_513_, v_x_514_, v_x_515_,
    );
    return v___x_516_;
}
pub unsafe fn l_Lean_PrefixTreeNode_find_x3f___redArg(
    mut v_cmp_517_: *mut LeanObject,
    mut v_t_518_: *mut LeanObject,
    mut v_k_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    v___x_520_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_517_, v_t_518_, v_k_519_,
    );
    return v___x_520_;
}
pub unsafe fn l_Lean_PrefixTreeNode_find_x3f(
    mut v_00_u03b1_521_: *mut LeanObject,
    mut v_00_u03b2_522_: *mut LeanObject,
    mut v_cmp_523_: *mut LeanObject,
    mut v_t_524_: *mut LeanObject,
    mut v_k_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    v___x_526_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_523_, v_t_524_, v_k_525_,
    );
    return v___x_526_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
    mut v_cmp_527_: *mut LeanObject,
    mut v_acc_x3f_528_: *mut LeanObject,
    mut v_x_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_530_) == 0 {
                    lean_dec_ref(v_cmp_527_);
                    v_a_531_ = lean_ctor_get(v_x_529_, 0);
                    lean_inc(v_a_531_);
                    lean_dec_ref(v_x_529_);
                    if lean_obj_tag(v_a_531_) == 0 {
                        return v_acc_x3f_528_;
                    } else {
                        lean_dec(v_acc_x3f_528_);
                        return v_a_531_;
                    }
                } else {
                    v_a_532_ = lean_ctor_get(v_x_529_, 0);
                    lean_inc(v_a_532_);
                    v_a_533_ = lean_ctor_get(v_x_529_, 1);
                    lean_inc(v_a_533_);
                    lean_dec_ref(v_x_529_);
                    v_head_534_ = lean_ctor_get(v_x_530_, 0);
                    lean_inc(v_head_534_);
                    v_tail_535_ = lean_ctor_get(v_x_530_, 1);
                    lean_inc(v_tail_535_);
                    lean_dec_ref_known(v_x_530_, 2);
                    lean_inc_ref(v_cmp_527_);
                    v___x_536_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_527_,
                        v_a_533_,
                        v_head_534_,
                    );
                    if lean_obj_tag(v___x_536_) == 0 {
                        lean_dec(v_tail_535_);
                        lean_dec(v_acc_x3f_528_);
                        lean_dec_ref(v_cmp_527_);
                        return v_a_532_;
                    } else {
                        if lean_obj_tag(v_a_532_) == 0 {
                            v_val_537_ = lean_ctor_get(v___x_536_, 0);
                            lean_inc(v_val_537_);
                            lean_dec_ref_known(v___x_536_, 1);
                            v_x_529_ = v_val_537_;
                            v_x_530_ = v_tail_535_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_acc_x3f_528_);
                            v_val_539_ = lean_ctor_get(v___x_536_, 0);
                            lean_inc(v_val_539_);
                            lean_dec_ref_known(v___x_536_, 1);
                            v_acc_x3f_528_ = v_a_532_;
                            v_x_529_ = v_val_539_;
                            v_x_530_ = v_tail_535_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop(
    mut v_00_u03b1_541_: *mut LeanObject,
    mut v_00_u03b2_542_: *mut LeanObject,
    mut v_cmp_543_: *mut LeanObject,
    mut v_acc_x3f_544_: *mut LeanObject,
    mut v_x_545_: *mut LeanObject,
    mut v_x_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    v___x_547_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_cmp_543_,
            v_acc_x3f_544_,
            v_x_545_,
            v_x_546_,
        );
    return v___x_547_;
}
pub unsafe fn l_Lean_PrefixTreeNode_findLongestPrefix_x3f___redArg(
    mut v_cmp_548_: *mut LeanObject,
    mut v_t_549_: *mut LeanObject,
    mut v_k_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    v___x_551_ = lean_box(0);
    v___x_552_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_cmp_548_, v___x_551_, v_t_549_, v_k_550_,
        );
    return v___x_552_;
}
pub unsafe fn l_Lean_PrefixTreeNode_findLongestPrefix_x3f(
    mut v_00_u03b1_553_: *mut LeanObject,
    mut v_00_u03b2_554_: *mut LeanObject,
    mut v_cmp_555_: *mut LeanObject,
    mut v_t_556_: *mut LeanObject,
    mut v_k_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = lean_box(0);
    v___x_559_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_cmp_555_, v___x_558_, v_t_556_, v_k_557_,
        );
    return v___x_559_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(
    mut v_inst_560_: *mut LeanObject,
    mut v___f_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
    mut v_d_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ =
        l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_560_, v___f_561_, v_d_563_, v_a_562_);
    return v___x_564_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(
    mut v_inst_565_: *mut LeanObject,
    mut v_f_566_: *mut LeanObject,
    mut v_d_567_: *mut LeanObject,
    mut v_x_568_: *mut LeanObject,
    mut v_t_569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_570_: *mut LeanObject = core::ptr::null_mut();
    v_res_570_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(v_inst_565_, v_f_566_, v_d_567_, v_x_568_, v_t_569_);
    lean_dec(v_x_568_);
    return v_res_570_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(
    mut v_inst_571_: *mut LeanObject,
    mut v_f_572_: *mut LeanObject,
    mut v_a_573_: *mut LeanObject,
    mut v_a_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_580_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_575_ = lean_ctor_get(v_inst_571_, 0);
    v_toBind_576_ = lean_ctor_get(v_inst_571_, 1);
    lean_inc(v_toBind_576_);
    v_toPure_577_ = lean_ctor_get(v_toApplicative_575_, 1);
    v_a_578_ = lean_ctor_get(v_a_573_, 0);
    lean_inc(v_a_578_);
    v_a_579_ = lean_ctor_get(v_a_573_, 1);
    lean_inc(v_a_579_);
    lean_dec_ref(v_a_573_);
    lean_inc(v_f_572_);
    lean_inc_ref(v_inst_571_);
    v___f_580_ = lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___f_580_, 0, v_inst_571_);
    lean_closure_set(v___f_580_, 1, v_f_572_);
    if lean_obj_tag(v_a_578_) == 0 {
        let mut v___f_581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_toPure_577_);
        lean_dec(v_f_572_);
        v___f_581_ = lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1 as *mut core::ffi::c_void, 4, 3);
        lean_closure_set(v___f_581_, 0, v_inst_571_);
        lean_closure_set(v___f_581_, 1, v___f_580_);
        lean_closure_set(v___f_581_, 2, v_a_579_);
        v___x_582_ = lean_apply_2(v_toPure_577_, lean_box(0), v_a_574_);
        v___x_583_ = lean_apply_4(
            v_toBind_576_,
            lean_box(0),
            lean_box(0),
            v___x_582_,
            v___f_581_,
        );
        return v___x_583_;
    } else {
        let mut v_val_584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_585_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
        v_val_584_ = lean_ctor_get(v_a_578_, 0);
        lean_inc(v_val_584_);
        lean_dec_ref_known(v_a_578_, 1);
        v___f_585_ = lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1 as *mut core::ffi::c_void, 4, 3);
        lean_closure_set(v___f_585_, 0, v_inst_571_);
        lean_closure_set(v___f_585_, 1, v___f_580_);
        lean_closure_set(v___f_585_, 2, v_a_579_);
        v___x_586_ = lean_apply_2(v_f_572_, v_val_584_, v_a_574_);
        v___x_587_ = lean_apply_4(
            v_toBind_576_,
            lean_box(0),
            lean_box(0),
            v___x_586_,
            v___f_585_,
        );
        return v___x_587_;
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(
    mut v_inst_588_: *mut LeanObject,
    mut v_f_589_: *mut LeanObject,
    mut v_d_590_: *mut LeanObject,
    mut v_x_591_: *mut LeanObject,
    mut v_t_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_593_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(
            v_inst_588_,
            v_f_589_,
            v_t_592_,
            v_d_590_,
        );
    return v___x_593_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(
    mut v_m_594_: *mut LeanObject,
    mut v_00_u03b1_595_: *mut LeanObject,
    mut v_00_u03b2_596_: *mut LeanObject,
    mut v_00_u03c3_597_: *mut LeanObject,
    mut v_inst_598_: *mut LeanObject,
    mut v_cmp_599_: *mut LeanObject,
    mut v_f_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
    mut v_a_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    v___x_603_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(
            v_inst_598_,
            v_f_600_,
            v_a_601_,
            v_a_602_,
        );
    return v___x_603_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___boxed(
    mut v_m_604_: *mut LeanObject,
    mut v_00_u03b1_605_: *mut LeanObject,
    mut v_00_u03b2_606_: *mut LeanObject,
    mut v_00_u03c3_607_: *mut LeanObject,
    mut v_inst_608_: *mut LeanObject,
    mut v_cmp_609_: *mut LeanObject,
    mut v_f_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_613_: *mut LeanObject = core::ptr::null_mut();
    v_res_613_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold(
        v_m_604_,
        v_00_u03b1_605_,
        v_00_u03b2_606_,
        v_00_u03c3_607_,
        v_inst_608_,
        v_cmp_609_,
        v_f_610_,
        v_a_611_,
        v_a_612_,
    );
    lean_dec_ref(v_cmp_609_);
    return v_res_613_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
    mut v_inst_614_: *mut LeanObject,
    mut v_cmp_615_: *mut LeanObject,
    mut v_init_616_: *mut LeanObject,
    mut v_f_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_618_) == 0 {
                    lean_dec(v_init_616_);
                    lean_dec_ref(v_cmp_615_);
                    v___x_621_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_614_, v_f_617_, v_a_619_, v_a_620_);
                    return v___x_621_;
                } else {
                    v_toApplicative_622_ = lean_ctor_get(v_inst_614_, 0);
                    v_toPure_623_ = lean_ctor_get(v_toApplicative_622_, 1);
                    v_head_624_ = lean_ctor_get(v_a_618_, 0);
                    lean_inc(v_head_624_);
                    v_tail_625_ = lean_ctor_get(v_a_618_, 1);
                    lean_inc(v_tail_625_);
                    lean_dec_ref_known(v_a_618_, 2);
                    v_a_626_ = lean_ctor_get(v_a_619_, 1);
                    lean_inc(v_a_626_);
                    lean_dec_ref(v_a_619_);
                    lean_inc_ref(v_cmp_615_);
                    v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_615_,
                        v_a_626_,
                        v_head_624_,
                    );
                    if lean_obj_tag(v___x_627_) == 0 {
                        lean_inc(v_toPure_623_);
                        lean_dec(v_tail_625_);
                        lean_dec(v_a_620_);
                        lean_dec(v_f_617_);
                        lean_dec_ref(v_cmp_615_);
                        lean_dec_ref(v_inst_614_);
                        v___x_628_ = lean_apply_2(v_toPure_623_, lean_box(0), v_init_616_);
                        return v___x_628_;
                    } else {
                        v_val_629_ = lean_ctor_get(v___x_627_, 0);
                        lean_inc(v_val_629_);
                        lean_dec_ref_known(v___x_627_, 1);
                        v_a_618_ = v_tail_625_;
                        v_a_619_ = v_val_629_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find(
    mut v_m_631_: *mut LeanObject,
    mut v_00_u03b1_632_: *mut LeanObject,
    mut v_00_u03b2_633_: *mut LeanObject,
    mut v_00_u03c3_634_: *mut LeanObject,
    mut v_inst_635_: *mut LeanObject,
    mut v_cmp_636_: *mut LeanObject,
    mut v_init_637_: *mut LeanObject,
    mut v_f_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    v___x_642_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_635_,
            v_cmp_636_,
            v_init_637_,
            v_f_638_,
            v_a_639_,
            v_a_640_,
            v_a_641_,
        );
    return v___x_642_;
}
pub unsafe fn l_Lean_PrefixTreeNode_foldMatchingM___redArg(
    mut v_inst_643_: *mut LeanObject,
    mut v_cmp_644_: *mut LeanObject,
    mut v_t_645_: *mut LeanObject,
    mut v_k_646_: *mut LeanObject,
    mut v_init_647_: *mut LeanObject,
    mut v_f_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_init_647_);
    v___x_649_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_643_,
            v_cmp_644_,
            v_init_647_,
            v_f_648_,
            v_k_646_,
            v_t_645_,
            v_init_647_,
        );
    return v___x_649_;
}
pub unsafe fn l_Lean_PrefixTreeNode_foldMatchingM(
    mut v_m_650_: *mut LeanObject,
    mut v_00_u03b1_651_: *mut LeanObject,
    mut v_00_u03b2_652_: *mut LeanObject,
    mut v_00_u03c3_653_: *mut LeanObject,
    mut v_inst_654_: *mut LeanObject,
    mut v_cmp_655_: *mut LeanObject,
    mut v_t_656_: *mut LeanObject,
    mut v_k_657_: *mut LeanObject,
    mut v_init_658_: *mut LeanObject,
    mut v_f_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_init_658_);
    v___x_660_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_654_,
            v_cmp_655_,
            v_init_658_,
            v_f_659_,
            v_k_657_,
            v_t_656_,
            v_init_658_,
        );
    return v___x_660_;
}
pub unsafe fn l_Lean_PrefixTree_empty___redArg(mut v_p_661_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_661_);
    return v___x_662_;
}
pub unsafe fn l_Lean_PrefixTree_empty___redArg___boxed(
    mut v_p_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_664_: *mut LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Lean_PrefixTree_empty___redArg(v_p_663_);
    lean_dec_ref(v_p_663_);
    return v_res_664_;
}
pub unsafe fn l_Lean_PrefixTree_empty(
    mut v_00_u03b1_665_: *mut LeanObject,
    mut v_00_u03b2_666_: *mut LeanObject,
    mut v_p_667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v___x_668_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_667_);
    return v___x_668_;
}
pub unsafe fn l_Lean_PrefixTree_empty___boxed(
    mut v_00_u03b1_669_: *mut LeanObject,
    mut v_00_u03b2_670_: *mut LeanObject,
    mut v_p_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_672_: *mut LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_PrefixTree_empty(v_00_u03b1_669_, v_00_u03b2_670_, v_p_671_);
    lean_dec_ref(v_p_671_);
    return v_res_672_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___redArg(
    mut v_p_673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    v___x_674_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_673_);
    return v___x_674_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___redArg___boxed(
    mut v_p_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_676_: *mut LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Lean_instInhabitedPrefixTree___redArg(v_p_675_);
    lean_dec_ref(v_p_675_);
    return v_res_676_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree(
    mut v_00_u03b1_677_: *mut LeanObject,
    mut v_00_u03b2_678_: *mut LeanObject,
    mut v_p_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_679_);
    return v___x_680_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___boxed(
    mut v_00_u03b1_681_: *mut LeanObject,
    mut v_00_u03b2_682_: *mut LeanObject,
    mut v_p_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_instInhabitedPrefixTree(v_00_u03b1_681_, v_00_u03b2_682_, v_p_683_);
    lean_dec_ref(v_p_683_);
    return v_res_684_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___redArg(
    mut v_p_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_685_);
    return v___x_686_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(
    mut v_p_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_688_: *mut LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_instEmptyCollectionPrefixTree___redArg(v_p_687_);
    lean_dec_ref(v_p_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree(
    mut v_00_u03b1_689_: *mut LeanObject,
    mut v_00_u03b2_690_: *mut LeanObject,
    mut v_p_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0), v_p_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___boxed(
    mut v_00_u03b1_693_: *mut LeanObject,
    mut v_00_u03b2_694_: *mut LeanObject,
    mut v_p_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_instEmptyCollectionPrefixTree(v_00_u03b1_693_, v_00_u03b2_694_, v_p_695_);
    lean_dec_ref(v_p_695_);
    return v_res_696_;
}
pub unsafe fn l_Lean_PrefixTree_insert___redArg(
    mut v_p_697_: *mut LeanObject,
    mut v_t_698_: *mut LeanObject,
    mut v_k_699_: *mut LeanObject,
    mut v_v_700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_701_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_p_697_, v_v_700_, v_t_698_, v_k_699_,
    );
    return v___x_701_;
}
pub unsafe fn l_Lean_PrefixTree_insert(
    mut v_00_u03b1_702_: *mut LeanObject,
    mut v_00_u03b2_703_: *mut LeanObject,
    mut v_p_704_: *mut LeanObject,
    mut v_t_705_: *mut LeanObject,
    mut v_k_706_: *mut LeanObject,
    mut v_v_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_p_704_, v_v_707_, v_t_705_, v_k_706_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_PrefixTree_find_x3f___redArg(
    mut v_p_709_: *mut LeanObject,
    mut v_t_710_: *mut LeanObject,
    mut v_k_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    v___x_712_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_p_709_, v_t_710_, v_k_711_,
    );
    return v___x_712_;
}
pub unsafe fn l_Lean_PrefixTree_find_x3f(
    mut v_00_u03b1_713_: *mut LeanObject,
    mut v_00_u03b2_714_: *mut LeanObject,
    mut v_p_715_: *mut LeanObject,
    mut v_t_716_: *mut LeanObject,
    mut v_k_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    v___x_718_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_p_715_, v_t_716_, v_k_717_,
    );
    return v___x_718_;
}
pub unsafe fn l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(
    mut v_p_719_: *mut LeanObject,
    mut v_t_720_: *mut LeanObject,
    mut v_k_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    v___x_722_ = lean_box(0);
    v___x_723_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_p_719_, v___x_722_, v_t_720_, v_k_721_,
        );
    return v___x_723_;
}
pub unsafe fn l_Lean_PrefixTree_findLongestPrefix_x3f(
    mut v_00_u03b1_724_: *mut LeanObject,
    mut v_00_u03b2_725_: *mut LeanObject,
    mut v_p_726_: *mut LeanObject,
    mut v_t_727_: *mut LeanObject,
    mut v_k_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = lean_box(0);
    v___x_730_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_p_726_, v___x_729_, v_t_727_, v_k_728_,
        );
    return v___x_730_;
}
pub unsafe fn l_Lean_PrefixTree_foldMatchingM___redArg(
    mut v_p_731_: *mut LeanObject,
    mut v_inst_732_: *mut LeanObject,
    mut v_t_733_: *mut LeanObject,
    mut v_k_734_: *mut LeanObject,
    mut v_init_735_: *mut LeanObject,
    mut v_f_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_init_735_);
    v___x_737_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_732_,
            v_p_731_,
            v_init_735_,
            v_f_736_,
            v_k_734_,
            v_t_733_,
            v_init_735_,
        );
    return v___x_737_;
}
pub unsafe fn l_Lean_PrefixTree_foldMatchingM(
    mut v_m_738_: *mut LeanObject,
    mut v_00_u03b1_739_: *mut LeanObject,
    mut v_00_u03b2_740_: *mut LeanObject,
    mut v_p_741_: *mut LeanObject,
    mut v_00_u03c3_742_: *mut LeanObject,
    mut v_inst_743_: *mut LeanObject,
    mut v_t_744_: *mut LeanObject,
    mut v_k_745_: *mut LeanObject,
    mut v_init_746_: *mut LeanObject,
    mut v_f_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_init_746_);
    v___x_748_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_743_,
            v_p_741_,
            v_init_746_,
            v_f_747_,
            v_k_745_,
            v_t_744_,
            v_init_746_,
        );
    return v___x_748_;
}
pub unsafe fn l_Lean_PrefixTree_foldM___redArg(
    mut v_p_749_: *mut LeanObject,
    mut v_inst_750_: *mut LeanObject,
    mut v_t_751_: *mut LeanObject,
    mut v_init_752_: *mut LeanObject,
    mut v_f_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = lean_box(0);
    lean_inc(v_init_752_);
    v___x_755_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_750_,
            v_p_749_,
            v_init_752_,
            v_f_753_,
            v___x_754_,
            v_t_751_,
            v_init_752_,
        );
    return v___x_755_;
}
pub unsafe fn l_Lean_PrefixTree_foldM(
    mut v_m_756_: *mut LeanObject,
    mut v_00_u03b1_757_: *mut LeanObject,
    mut v_00_u03b2_758_: *mut LeanObject,
    mut v_p_759_: *mut LeanObject,
    mut v_00_u03c3_760_: *mut LeanObject,
    mut v_inst_761_: *mut LeanObject,
    mut v_t_762_: *mut LeanObject,
    mut v_init_763_: *mut LeanObject,
    mut v_f_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_box(0);
    lean_inc(v_init_763_);
    v___x_766_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_761_,
            v_p_759_,
            v_init_763_,
            v_f_764_,
            v___x_765_,
            v_t_762_,
            v_init_763_,
        );
    return v___x_766_;
}
pub unsafe fn l_Lean_PrefixTree_forMatchingM___redArg___lam__0(
    mut v_f_767_: *mut LeanObject,
    mut v_b_768_: *mut LeanObject,
    mut v_x_769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = lean_apply_1(v_f_767_, v_b_768_);
    return v___x_770_;
}
pub unsafe fn l_Lean_PrefixTree_forMatchingM___redArg(
    mut v_p_771_: *mut LeanObject,
    mut v_inst_772_: *mut LeanObject,
    mut v_t_773_: *mut LeanObject,
    mut v_k_774_: *mut LeanObject,
    mut v_f_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___f_776_ = lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_776_, 0, v_f_775_);
    v___x_777_ = lean_box(0);
    v___x_778_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_772_,
            v_p_771_,
            v___x_777_,
            v___f_776_,
            v_k_774_,
            v_t_773_,
            v___x_777_,
        );
    return v___x_778_;
}
pub unsafe fn l_Lean_PrefixTree_forMatchingM(
    mut v_m_779_: *mut LeanObject,
    mut v_00_u03b1_780_: *mut LeanObject,
    mut v_00_u03b2_781_: *mut LeanObject,
    mut v_p_782_: *mut LeanObject,
    mut v_inst_783_: *mut LeanObject,
    mut v_t_784_: *mut LeanObject,
    mut v_k_785_: *mut LeanObject,
    mut v_f_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    v___f_787_ = lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_787_, 0, v_f_786_);
    v___x_788_ = lean_box(0);
    v___x_789_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_783_,
            v_p_782_,
            v___x_788_,
            v___f_787_,
            v_k_785_,
            v_t_784_,
            v___x_788_,
        );
    return v___x_789_;
}
pub unsafe fn l_Lean_PrefixTree_forM___redArg(
    mut v_p_790_: *mut LeanObject,
    mut v_inst_791_: *mut LeanObject,
    mut v_t_792_: *mut LeanObject,
    mut v_f_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___f_794_ = lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_794_, 0, v_f_793_);
    v___x_795_ = lean_box(0);
    v___x_796_ = lean_box(0);
    v___x_797_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_791_,
            v_p_790_,
            v___x_796_,
            v___f_794_,
            v___x_795_,
            v_t_792_,
            v___x_796_,
        );
    return v___x_797_;
}
pub unsafe fn l_Lean_PrefixTree_forM(
    mut v_m_798_: *mut LeanObject,
    mut v_00_u03b1_799_: *mut LeanObject,
    mut v_00_u03b2_800_: *mut LeanObject,
    mut v_p_801_: *mut LeanObject,
    mut v_inst_802_: *mut LeanObject,
    mut v_t_803_: *mut LeanObject,
    mut v_f_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___f_805_ = lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_805_, 0, v_f_804_);
    v___x_806_ = lean_box(0);
    v___x_807_ = lean_box(0);
    v___x_808_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
            v_inst_802_,
            v_p_801_,
            v___x_807_,
            v___f_805_,
            v___x_806_,
            v_t_803_,
            v___x_807_,
        );
    return v___x_808_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_PrefixTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PrefixTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_PrefixTree(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PrefixTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PrefixTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_PrefixTree(builtin);
}
