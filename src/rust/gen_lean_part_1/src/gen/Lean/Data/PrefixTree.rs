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
pub static l_Lean_instInhabitedPrefixTreeNode___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedPrefixTreeNode___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedPrefixTreeNode___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instInhabitedPrefixTreeNode(
    mut v_00_u03b1_408_: *mut leanh::LeanObject,
    mut v_00_u03b2_409_: *mut leanh::LeanObject,
    mut v_cmp_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = l_Lean_instInhabitedPrefixTreeNode___closed__0;
    return v___x_411_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTreeNode___boxed(
    mut v_00_u03b1_412_: *mut leanh::LeanObject,
    mut v_00_u03b2_413_: *mut leanh::LeanObject,
    mut v_cmp_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_Lean_instInhabitedPrefixTreeNode(v_00_u03b1_412_, v_00_u03b2_413_, v_cmp_414_);
    leanh::lean_dec_ref(v_cmp_414_);
    return v_res_415_;
}
pub unsafe fn l_Lean_PrefixTreeNode_empty(
    mut v_00_u03b1_416_: *mut leanh::LeanObject,
    mut v_00_u03b2_417_: *mut leanh::LeanObject,
    mut v_cmp_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = l_Lean_instInhabitedPrefixTreeNode___closed__0;
    return v___x_419_;
}
pub unsafe fn l_Lean_PrefixTreeNode_empty___boxed(
    mut v_00_u03b1_420_: *mut leanh::LeanObject,
    mut v_00_u03b2_421_: *mut leanh::LeanObject,
    mut v_cmp_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_PrefixTreeNode_empty(v_00_u03b1_420_, v_00_u03b2_421_, v_cmp_422_);
    leanh::lean_dec_ref(v_cmp_422_);
    return v_res_423_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(
    mut v_cmp_424_: *mut leanh::LeanObject,
    mut v_val_425_: *mut leanh::LeanObject,
    mut v_k_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v_t_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_442_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_k_426_) == 0 {
                    leanh::lean_dec_ref(v_cmp_424_);
                    v___x_427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_427_, 0, v_val_425_);
                    v___x_428_ = leanh::lean_box(1);
                    v___x_429_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_429_, 0, v___x_427_);
                    leanh::lean_ctor_set(v___x_429_, 1, v___x_428_);
                    return v___x_429_;
                } else {
                    v_head_430_ = leanh::lean_ctor_get(v_k_426_, 0);
                    v_tail_431_ = leanh::lean_ctor_get(v_k_426_, 1);
                    v_isSharedCheck_442_ = (!leanh::lean_is_exclusive(v_k_426_)) as u8;
                    if v_isSharedCheck_442_ == 0 {
                        v___x_433_ = v_k_426_;
                        v_isShared_434_ = v_isSharedCheck_442_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_431_);
                        leanh::lean_inc(v_head_430_);
                        leanh::lean_dec(v_k_426_);
                        v___x_433_ = leanh::lean_box(0);
                        v_isShared_434_ = v_isSharedCheck_442_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_cmp_424_);
                v_t_435_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_424_, v_val_425_, v_tail_431_);
                v___x_436_ = leanh::lean_box(0);
                v___x_437_ = leanh::lean_box(1);
                v___x_438_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
                    v_cmp_424_,
                    v_head_430_,
                    v_t_435_,
                    v___x_437_,
                );
                if v_isShared_434_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_433_, 0);
                    leanh::lean_ctor_set(v___x_433_, 1, v___x_438_);
                    leanh::lean_ctor_set(v___x_433_, 0, v___x_436_);
                    v___x_440_ = v___x_433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
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
    mut v_00_u03b1_443_: *mut leanh::LeanObject,
    mut v_00_u03b2_444_: *mut leanh::LeanObject,
    mut v_cmp_445_: *mut leanh::LeanObject,
    mut v_val_446_: *mut leanh::LeanObject,
    mut v_k_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(
            v_cmp_445_, v_val_446_, v_k_447_,
        );
    return v___x_448_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
    mut v_cmp_449_: *mut leanh::LeanObject,
    mut v_val_450_: *mut leanh::LeanObject,
    mut v_x_451_: *mut leanh::LeanObject,
    mut v_x_452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_456_: u8 = 0;
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut v_unused_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_467_: u8 = 0;
    let mut v_head_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_452_) == 0 {
                    leanh::lean_dec_ref(v_cmp_449_);
                    v_a_453_ = leanh::lean_ctor_get(v_x_451_, 1);
                    v_isSharedCheck_461_ = (!leanh::lean_is_exclusive(v_x_451_)) as u8;
                    if v_isSharedCheck_461_ == 0 {
                        v_unused_462_ = leanh::lean_ctor_get(v_x_451_, 0);
                        leanh::lean_dec(v_unused_462_);
                        v___x_455_ = v_x_451_;
                        v_isShared_456_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_453_);
                        leanh::lean_dec(v_x_451_);
                        v___x_455_ = leanh::lean_box(0);
                        v_isShared_456_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_463_ = leanh::lean_ctor_get(v_x_451_, 0);
                    v_a_464_ = leanh::lean_ctor_get(v_x_451_, 1);
                    v_isSharedCheck_480_ = (!leanh::lean_is_exclusive(v_x_451_)) as u8;
                    if v_isSharedCheck_480_ == 0 {
                        v___x_466_ = v_x_451_;
                        v_isShared_467_ = v_isSharedCheck_480_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_464_);
                        leanh::lean_inc(v_a_463_);
                        leanh::lean_dec(v_x_451_);
                        v___x_466_ = leanh::lean_box(0);
                        v_isShared_467_ = v_isSharedCheck_480_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_457_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_457_, 0, v_val_450_);
                if v_isShared_456_ == 0 {
                    leanh::lean_ctor_set(v___x_455_, 0, v___x_457_);
                    v___x_459_ = v___x_455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_460_, 1, v_a_453_);
                    v___x_459_ = v_reuseFailAlloc_460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_459_;
            }
            3 => {
                v_head_468_ = leanh::lean_ctor_get(v_x_452_, 0);
                leanh::lean_inc_n(v_head_468_, 2);
                v_tail_469_ = leanh::lean_ctor_get(v_x_452_, 1);
                leanh::lean_inc(v_tail_469_);
                leanh::lean_dec_ref_known(v_x_452_, 2);
                leanh::lean_inc(v_a_464_);
                leanh::lean_inc_ref(v_cmp_449_);
                v___x_476_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                    v_cmp_449_,
                    v_a_464_,
                    v_head_468_,
                );
                if leanh::lean_obj_tag(v___x_476_) == 0 {
                    leanh::lean_inc_ref(v_cmp_449_);
                    v___x_477_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_insertEmpty___redArg(v_cmp_449_, v_val_450_, v_tail_469_);
                    v___y_471_ = v___x_477_;
                    state = 4;
                    continue;
                } else {
                    v_val_478_ = leanh::lean_ctor_get(v___x_476_, 0);
                    leanh::lean_inc(v_val_478_);
                    leanh::lean_dec_ref_known(v___x_476_, 1);
                    leanh::lean_inc_ref(v_cmp_449_);
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
                    leanh::lean_ctor_set(v___x_466_, 1, v___x_472_);
                    v___x_474_ = v___x_466_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
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
    mut v_00_u03b1_481_: *mut leanh::LeanObject,
    mut v_00_u03b2_482_: *mut leanh::LeanObject,
    mut v_cmp_483_: *mut leanh::LeanObject,
    mut v_val_484_: *mut leanh::LeanObject,
    mut v_x_485_: *mut leanh::LeanObject,
    mut v_x_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_483_, v_val_484_, v_x_485_, v_x_486_,
    );
    return v___x_487_;
}
pub unsafe fn l_Lean_PrefixTreeNode_insert___redArg(
    mut v_cmp_488_: *mut leanh::LeanObject,
    mut v_t_489_: *mut leanh::LeanObject,
    mut v_k_490_: *mut leanh::LeanObject,
    mut v_val_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_488_, v_val_491_, v_t_489_, v_k_490_,
    );
    return v___x_492_;
}
pub unsafe fn l_Lean_PrefixTreeNode_insert(
    mut v_00_u03b1_493_: *mut leanh::LeanObject,
    mut v_00_u03b2_494_: *mut leanh::LeanObject,
    mut v_cmp_495_: *mut leanh::LeanObject,
    mut v_t_496_: *mut leanh::LeanObject,
    mut v_k_497_: *mut leanh::LeanObject,
    mut v_val_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_cmp_495_, v_val_498_, v_t_496_, v_k_497_,
    );
    return v___x_499_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
    mut v_cmp_500_: *mut leanh::LeanObject,
    mut v_x_501_: *mut leanh::LeanObject,
    mut v_x_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_502_) == 0 {
                    leanh::lean_dec_ref(v_cmp_500_);
                    v_a_503_ = leanh::lean_ctor_get(v_x_501_, 0);
                    leanh::lean_inc(v_a_503_);
                    leanh::lean_dec_ref(v_x_501_);
                    return v_a_503_;
                } else {
                    v_a_504_ = leanh::lean_ctor_get(v_x_501_, 1);
                    leanh::lean_inc(v_a_504_);
                    leanh::lean_dec_ref(v_x_501_);
                    v_head_505_ = leanh::lean_ctor_get(v_x_502_, 0);
                    leanh::lean_inc(v_head_505_);
                    v_tail_506_ = leanh::lean_ctor_get(v_x_502_, 1);
                    leanh::lean_inc(v_tail_506_);
                    leanh::lean_dec_ref_known(v_x_502_, 2);
                    leanh::lean_inc_ref(v_cmp_500_);
                    v___x_507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_500_,
                        v_a_504_,
                        v_head_505_,
                    );
                    if leanh::lean_obj_tag(v___x_507_) == 0 {
                        leanh::lean_dec(v_tail_506_);
                        leanh::lean_dec_ref(v_cmp_500_);
                        v___x_508_ = leanh::lean_box(0);
                        return v___x_508_;
                    } else {
                        v_val_509_ = leanh::lean_ctor_get(v___x_507_, 0);
                        leanh::lean_inc(v_val_509_);
                        leanh::lean_dec_ref_known(v___x_507_, 1);
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
    mut v_00_u03b1_511_: *mut leanh::LeanObject,
    mut v_00_u03b2_512_: *mut leanh::LeanObject,
    mut v_cmp_513_: *mut leanh::LeanObject,
    mut v_x_514_: *mut leanh::LeanObject,
    mut v_x_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_513_, v_x_514_, v_x_515_,
    );
    return v___x_516_;
}
pub unsafe fn l_Lean_PrefixTreeNode_find_x3f___redArg(
    mut v_cmp_517_: *mut leanh::LeanObject,
    mut v_t_518_: *mut leanh::LeanObject,
    mut v_k_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_520_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_517_, v_t_518_, v_k_519_,
    );
    return v___x_520_;
}
pub unsafe fn l_Lean_PrefixTreeNode_find_x3f(
    mut v_00_u03b1_521_: *mut leanh::LeanObject,
    mut v_00_u03b2_522_: *mut leanh::LeanObject,
    mut v_cmp_523_: *mut leanh::LeanObject,
    mut v_t_524_: *mut leanh::LeanObject,
    mut v_k_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_cmp_523_, v_t_524_, v_k_525_,
    );
    return v___x_526_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
    mut v_cmp_527_: *mut leanh::LeanObject,
    mut v_acc_x3f_528_: *mut leanh::LeanObject,
    mut v_x_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_530_) == 0 {
                    leanh::lean_dec_ref(v_cmp_527_);
                    v_a_531_ = leanh::lean_ctor_get(v_x_529_, 0);
                    leanh::lean_inc(v_a_531_);
                    leanh::lean_dec_ref(v_x_529_);
                    if leanh::lean_obj_tag(v_a_531_) == 0 {
                        return v_acc_x3f_528_;
                    } else {
                        leanh::lean_dec(v_acc_x3f_528_);
                        return v_a_531_;
                    }
                } else {
                    v_a_532_ = leanh::lean_ctor_get(v_x_529_, 0);
                    leanh::lean_inc(v_a_532_);
                    v_a_533_ = leanh::lean_ctor_get(v_x_529_, 1);
                    leanh::lean_inc(v_a_533_);
                    leanh::lean_dec_ref(v_x_529_);
                    v_head_534_ = leanh::lean_ctor_get(v_x_530_, 0);
                    leanh::lean_inc(v_head_534_);
                    v_tail_535_ = leanh::lean_ctor_get(v_x_530_, 1);
                    leanh::lean_inc(v_tail_535_);
                    leanh::lean_dec_ref_known(v_x_530_, 2);
                    leanh::lean_inc_ref(v_cmp_527_);
                    v___x_536_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_527_,
                        v_a_533_,
                        v_head_534_,
                    );
                    if leanh::lean_obj_tag(v___x_536_) == 0 {
                        leanh::lean_dec(v_tail_535_);
                        leanh::lean_dec(v_acc_x3f_528_);
                        leanh::lean_dec_ref(v_cmp_527_);
                        return v_a_532_;
                    } else {
                        if leanh::lean_obj_tag(v_a_532_) == 0 {
                            v_val_537_ = leanh::lean_ctor_get(v___x_536_, 0);
                            leanh::lean_inc(v_val_537_);
                            leanh::lean_dec_ref_known(v___x_536_, 1);
                            v_x_529_ = v_val_537_;
                            v_x_530_ = v_tail_535_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_acc_x3f_528_);
                            v_val_539_ = leanh::lean_ctor_get(v___x_536_, 0);
                            leanh::lean_inc(v_val_539_);
                            leanh::lean_dec_ref_known(v___x_536_, 1);
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
    mut v_00_u03b1_541_: *mut leanh::LeanObject,
    mut v_00_u03b2_542_: *mut leanh::LeanObject,
    mut v_cmp_543_: *mut leanh::LeanObject,
    mut v_acc_x3f_544_: *mut leanh::LeanObject,
    mut v_x_545_: *mut leanh::LeanObject,
    mut v_x_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cmp_548_: *mut leanh::LeanObject,
    mut v_t_549_: *mut leanh::LeanObject,
    mut v_k_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = leanh::lean_box(0);
    v___x_552_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_cmp_548_, v___x_551_, v_t_549_, v_k_550_,
        );
    return v___x_552_;
}
pub unsafe fn l_Lean_PrefixTreeNode_findLongestPrefix_x3f(
    mut v_00_u03b1_553_: *mut leanh::LeanObject,
    mut v_00_u03b2_554_: *mut leanh::LeanObject,
    mut v_cmp_555_: *mut leanh::LeanObject,
    mut v_t_556_: *mut leanh::LeanObject,
    mut v_k_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = leanh::lean_box(0);
    v___x_559_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_cmp_555_, v___x_558_, v_t_556_, v_k_557_,
        );
    return v___x_559_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1(
    mut v_inst_560_: *mut leanh::LeanObject,
    mut v___f_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
    mut v_d_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ =
        l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_560_, v___f_561_, v_d_563_, v_a_562_);
    return v___x_564_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed(
    mut v_inst_565_: *mut leanh::LeanObject,
    mut v_f_566_: *mut leanh::LeanObject,
    mut v_d_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
    mut v_t_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_570_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(v_inst_565_, v_f_566_, v_d_567_, v_x_568_, v_t_569_);
    leanh::lean_dec(v_x_568_);
    return v_res_570_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(
    mut v_inst_571_: *mut leanh::LeanObject,
    mut v_f_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_575_ = leanh::lean_ctor_get(v_inst_571_, 0);
    v_toBind_576_ = leanh::lean_ctor_get(v_inst_571_, 1);
    leanh::lean_inc(v_toBind_576_);
    v_toPure_577_ = leanh::lean_ctor_get(v_toApplicative_575_, 1);
    v_a_578_ = leanh::lean_ctor_get(v_a_573_, 0);
    leanh::lean_inc(v_a_578_);
    v_a_579_ = leanh::lean_ctor_get(v_a_573_, 1);
    leanh::lean_inc(v_a_579_);
    leanh::lean_dec_ref(v_a_573_);
    leanh::lean_inc(v_f_572_);
    leanh::lean_inc_ref(v_inst_571_);
    v___f_580_ = leanh::lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
    leanh::lean_closure_set(v___f_580_, 0, v_inst_571_);
    leanh::lean_closure_set(v___f_580_, 1, v_f_572_);
    if leanh::lean_obj_tag(v_a_578_) == 0 {
        let mut v___f_581_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_toPure_577_);
        leanh::lean_dec(v_f_572_);
        v___f_581_ = leanh::lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1 as *mut core::ffi::c_void, 4, 3);
        leanh::lean_closure_set(v___f_581_, 0, v_inst_571_);
        leanh::lean_closure_set(v___f_581_, 1, v___f_580_);
        leanh::lean_closure_set(v___f_581_, 2, v_a_579_);
        v___x_582_ = leanh::lean_apply_2(v_toPure_577_, leanh::lean_box(0), v_a_574_);
        v___x_583_ = leanh::lean_apply_4(
            v_toBind_576_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_582_,
            v___f_581_,
        );
        return v___x_583_;
    } else {
        let mut v_val_584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_584_ = leanh::lean_ctor_get(v_a_578_, 0);
        leanh::lean_inc(v_val_584_);
        leanh::lean_dec_ref_known(v_a_578_, 1);
        v___f_585_ = leanh::lean_alloc_closure(l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__1 as *mut core::ffi::c_void, 4, 3);
        leanh::lean_closure_set(v___f_585_, 0, v_inst_571_);
        leanh::lean_closure_set(v___f_585_, 1, v___f_580_);
        leanh::lean_closure_set(v___f_585_, 2, v_a_579_);
        v___x_586_ = leanh::lean_apply_2(v_f_572_, v_val_584_, v_a_574_);
        v___x_587_ = leanh::lean_apply_4(
            v_toBind_576_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_586_,
            v___f_585_,
        );
        return v___x_587_;
    }
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg___lam__0(
    mut v_inst_588_: *mut leanh::LeanObject,
    mut v_f_589_: *mut leanh::LeanObject,
    mut v_d_590_: *mut leanh::LeanObject,
    mut v_x_591_: *mut leanh::LeanObject,
    mut v_t_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_594_: *mut leanh::LeanObject,
    mut v_00_u03b1_595_: *mut leanh::LeanObject,
    mut v_00_u03b2_596_: *mut leanh::LeanObject,
    mut v_00_u03c3_597_: *mut leanh::LeanObject,
    mut v_inst_598_: *mut leanh::LeanObject,
    mut v_cmp_599_: *mut leanh::LeanObject,
    mut v_f_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_604_: *mut leanh::LeanObject,
    mut v_00_u03b1_605_: *mut leanh::LeanObject,
    mut v_00_u03b2_606_: *mut leanh::LeanObject,
    mut v_00_u03c3_607_: *mut leanh::LeanObject,
    mut v_inst_608_: *mut leanh::LeanObject,
    mut v_cmp_609_: *mut leanh::LeanObject,
    mut v_f_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
    mut v_a_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_613_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v_cmp_609_);
    return v_res_613_;
}
pub unsafe fn l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_find___redArg(
    mut v_inst_614_: *mut leanh::LeanObject,
    mut v_cmp_615_: *mut leanh::LeanObject,
    mut v_init_616_: *mut leanh::LeanObject,
    mut v_f_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
    mut v_a_619_: *mut leanh::LeanObject,
    mut v_a_620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_618_) == 0 {
                    leanh::lean_dec(v_init_616_);
                    leanh::lean_dec_ref(v_cmp_615_);
                    v___x_621_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_foldMatchingM_fold___redArg(v_inst_614_, v_f_617_, v_a_619_, v_a_620_);
                    return v___x_621_;
                } else {
                    v_toApplicative_622_ = leanh::lean_ctor_get(v_inst_614_, 0);
                    v_toPure_623_ = leanh::lean_ctor_get(v_toApplicative_622_, 1);
                    v_head_624_ = leanh::lean_ctor_get(v_a_618_, 0);
                    leanh::lean_inc(v_head_624_);
                    v_tail_625_ = leanh::lean_ctor_get(v_a_618_, 1);
                    leanh::lean_inc(v_tail_625_);
                    leanh::lean_dec_ref_known(v_a_618_, 2);
                    v_a_626_ = leanh::lean_ctor_get(v_a_619_, 1);
                    leanh::lean_inc(v_a_626_);
                    leanh::lean_dec_ref(v_a_619_);
                    leanh::lean_inc_ref(v_cmp_615_);
                    v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(
                        v_cmp_615_,
                        v_a_626_,
                        v_head_624_,
                    );
                    if leanh::lean_obj_tag(v___x_627_) == 0 {
                        leanh::lean_inc(v_toPure_623_);
                        leanh::lean_dec(v_tail_625_);
                        leanh::lean_dec(v_a_620_);
                        leanh::lean_dec(v_f_617_);
                        leanh::lean_dec_ref(v_cmp_615_);
                        leanh::lean_dec_ref(v_inst_614_);
                        v___x_628_ = leanh::lean_apply_2(
                            v_toPure_623_,
                            leanh::lean_box(0),
                            v_init_616_,
                        );
                        return v___x_628_;
                    } else {
                        v_val_629_ = leanh::lean_ctor_get(v___x_627_, 0);
                        leanh::lean_inc(v_val_629_);
                        leanh::lean_dec_ref_known(v___x_627_, 1);
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
    mut v_m_631_: *mut leanh::LeanObject,
    mut v_00_u03b1_632_: *mut leanh::LeanObject,
    mut v_00_u03b2_633_: *mut leanh::LeanObject,
    mut v_00_u03c3_634_: *mut leanh::LeanObject,
    mut v_inst_635_: *mut leanh::LeanObject,
    mut v_cmp_636_: *mut leanh::LeanObject,
    mut v_init_637_: *mut leanh::LeanObject,
    mut v_f_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
    mut v_a_640_: *mut leanh::LeanObject,
    mut v_a_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_643_: *mut leanh::LeanObject,
    mut v_cmp_644_: *mut leanh::LeanObject,
    mut v_t_645_: *mut leanh::LeanObject,
    mut v_k_646_: *mut leanh::LeanObject,
    mut v_init_647_: *mut leanh::LeanObject,
    mut v_f_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_init_647_);
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
    mut v_m_650_: *mut leanh::LeanObject,
    mut v_00_u03b1_651_: *mut leanh::LeanObject,
    mut v_00_u03b2_652_: *mut leanh::LeanObject,
    mut v_00_u03c3_653_: *mut leanh::LeanObject,
    mut v_inst_654_: *mut leanh::LeanObject,
    mut v_cmp_655_: *mut leanh::LeanObject,
    mut v_t_656_: *mut leanh::LeanObject,
    mut v_k_657_: *mut leanh::LeanObject,
    mut v_init_658_: *mut leanh::LeanObject,
    mut v_f_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_init_658_);
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
pub unsafe fn l_Lean_PrefixTree_empty___redArg(
    mut v_p_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_661_,
    );
    return v___x_662_;
}
pub unsafe fn l_Lean_PrefixTree_empty___redArg___boxed(
    mut v_p_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Lean_PrefixTree_empty___redArg(v_p_663_);
    leanh::lean_dec_ref(v_p_663_);
    return v_res_664_;
}
pub unsafe fn l_Lean_PrefixTree_empty(
    mut v_00_u03b1_665_: *mut leanh::LeanObject,
    mut v_00_u03b2_666_: *mut leanh::LeanObject,
    mut v_p_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_668_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_667_,
    );
    return v___x_668_;
}
pub unsafe fn l_Lean_PrefixTree_empty___boxed(
    mut v_00_u03b1_669_: *mut leanh::LeanObject,
    mut v_00_u03b2_670_: *mut leanh::LeanObject,
    mut v_p_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_PrefixTree_empty(v_00_u03b1_669_, v_00_u03b2_670_, v_p_671_);
    leanh::lean_dec_ref(v_p_671_);
    return v_res_672_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___redArg(
    mut v_p_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_674_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_673_,
    );
    return v___x_674_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___redArg___boxed(
    mut v_p_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Lean_instInhabitedPrefixTree___redArg(v_p_675_);
    leanh::lean_dec_ref(v_p_675_);
    return v_res_676_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree(
    mut v_00_u03b1_677_: *mut leanh::LeanObject,
    mut v_00_u03b2_678_: *mut leanh::LeanObject,
    mut v_p_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_679_,
    );
    return v___x_680_;
}
pub unsafe fn l_Lean_instInhabitedPrefixTree___boxed(
    mut v_00_u03b1_681_: *mut leanh::LeanObject,
    mut v_00_u03b2_682_: *mut leanh::LeanObject,
    mut v_p_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_instInhabitedPrefixTree(v_00_u03b1_681_, v_00_u03b2_682_, v_p_683_);
    leanh::lean_dec_ref(v_p_683_);
    return v_res_684_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___redArg(
    mut v_p_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_685_,
    );
    return v___x_686_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___redArg___boxed(
    mut v_p_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_instEmptyCollectionPrefixTree___redArg(v_p_687_);
    leanh::lean_dec_ref(v_p_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree(
    mut v_00_u03b1_689_: *mut leanh::LeanObject,
    mut v_00_u03b2_690_: *mut leanh::LeanObject,
    mut v_p_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Lean_PrefixTreeNode_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_p_691_,
    );
    return v___x_692_;
}
pub unsafe fn l_Lean_instEmptyCollectionPrefixTree___boxed(
    mut v_00_u03b1_693_: *mut leanh::LeanObject,
    mut v_00_u03b2_694_: *mut leanh::LeanObject,
    mut v_p_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_instEmptyCollectionPrefixTree(v_00_u03b1_693_, v_00_u03b2_694_, v_p_695_);
    leanh::lean_dec_ref(v_p_695_);
    return v_res_696_;
}
pub unsafe fn l_Lean_PrefixTree_insert___redArg(
    mut v_p_697_: *mut leanh::LeanObject,
    mut v_t_698_: *mut leanh::LeanObject,
    mut v_k_699_: *mut leanh::LeanObject,
    mut v_v_700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_701_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_p_697_, v_v_700_, v_t_698_, v_k_699_,
    );
    return v___x_701_;
}
pub unsafe fn l_Lean_PrefixTree_insert(
    mut v_00_u03b1_702_: *mut leanh::LeanObject,
    mut v_00_u03b2_703_: *mut leanh::LeanObject,
    mut v_p_704_: *mut leanh::LeanObject,
    mut v_t_705_: *mut leanh::LeanObject,
    mut v_k_706_: *mut leanh::LeanObject,
    mut v_v_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_insert_loop___redArg(
        v_p_704_, v_v_707_, v_t_705_, v_k_706_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_PrefixTree_find_x3f___redArg(
    mut v_p_709_: *mut leanh::LeanObject,
    mut v_t_710_: *mut leanh::LeanObject,
    mut v_k_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_p_709_, v_t_710_, v_k_711_,
    );
    return v___x_712_;
}
pub unsafe fn l_Lean_PrefixTree_find_x3f(
    mut v_00_u03b1_713_: *mut leanh::LeanObject,
    mut v_00_u03b2_714_: *mut leanh::LeanObject,
    mut v_p_715_: *mut leanh::LeanObject,
    mut v_t_716_: *mut leanh::LeanObject,
    mut v_k_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_718_ = l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_find_x3f_loop___redArg(
        v_p_715_, v_t_716_, v_k_717_,
    );
    return v___x_718_;
}
pub unsafe fn l_Lean_PrefixTree_findLongestPrefix_x3f___redArg(
    mut v_p_719_: *mut leanh::LeanObject,
    mut v_t_720_: *mut leanh::LeanObject,
    mut v_k_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = leanh::lean_box(0);
    v___x_723_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_p_719_, v___x_722_, v_t_720_, v_k_721_,
        );
    return v___x_723_;
}
pub unsafe fn l_Lean_PrefixTree_findLongestPrefix_x3f(
    mut v_00_u03b1_724_: *mut leanh::LeanObject,
    mut v_00_u03b2_725_: *mut leanh::LeanObject,
    mut v_p_726_: *mut leanh::LeanObject,
    mut v_t_727_: *mut leanh::LeanObject,
    mut v_k_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = leanh::lean_box(0);
    v___x_730_ =
        l___private_Lean_Data_PrefixTree_0__Lean_PrefixTreeNode_findLongestPrefix_x3f_loop___redArg(
            v_p_726_, v___x_729_, v_t_727_, v_k_728_,
        );
    return v___x_730_;
}
pub unsafe fn l_Lean_PrefixTree_foldMatchingM___redArg(
    mut v_p_731_: *mut leanh::LeanObject,
    mut v_inst_732_: *mut leanh::LeanObject,
    mut v_t_733_: *mut leanh::LeanObject,
    mut v_k_734_: *mut leanh::LeanObject,
    mut v_init_735_: *mut leanh::LeanObject,
    mut v_f_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_init_735_);
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
    mut v_m_738_: *mut leanh::LeanObject,
    mut v_00_u03b1_739_: *mut leanh::LeanObject,
    mut v_00_u03b2_740_: *mut leanh::LeanObject,
    mut v_p_741_: *mut leanh::LeanObject,
    mut v_00_u03c3_742_: *mut leanh::LeanObject,
    mut v_inst_743_: *mut leanh::LeanObject,
    mut v_t_744_: *mut leanh::LeanObject,
    mut v_k_745_: *mut leanh::LeanObject,
    mut v_init_746_: *mut leanh::LeanObject,
    mut v_f_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_init_746_);
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
    mut v_p_749_: *mut leanh::LeanObject,
    mut v_inst_750_: *mut leanh::LeanObject,
    mut v_t_751_: *mut leanh::LeanObject,
    mut v_init_752_: *mut leanh::LeanObject,
    mut v_f_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = leanh::lean_box(0);
    leanh::lean_inc(v_init_752_);
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
    mut v_m_756_: *mut leanh::LeanObject,
    mut v_00_u03b1_757_: *mut leanh::LeanObject,
    mut v_00_u03b2_758_: *mut leanh::LeanObject,
    mut v_p_759_: *mut leanh::LeanObject,
    mut v_00_u03c3_760_: *mut leanh::LeanObject,
    mut v_inst_761_: *mut leanh::LeanObject,
    mut v_t_762_: *mut leanh::LeanObject,
    mut v_init_763_: *mut leanh::LeanObject,
    mut v_f_764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = leanh::lean_box(0);
    leanh::lean_inc(v_init_763_);
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
    mut v_f_767_: *mut leanh::LeanObject,
    mut v_b_768_: *mut leanh::LeanObject,
    mut v_x_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = leanh::lean_apply_1(v_f_767_, v_b_768_);
    return v___x_770_;
}
pub unsafe fn l_Lean_PrefixTree_forMatchingM___redArg(
    mut v_p_771_: *mut leanh::LeanObject,
    mut v_inst_772_: *mut leanh::LeanObject,
    mut v_t_773_: *mut leanh::LeanObject,
    mut v_k_774_: *mut leanh::LeanObject,
    mut v_f_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_776_ = leanh::lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_776_, 0, v_f_775_);
    v___x_777_ = leanh::lean_box(0);
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
    mut v_m_779_: *mut leanh::LeanObject,
    mut v_00_u03b1_780_: *mut leanh::LeanObject,
    mut v_00_u03b2_781_: *mut leanh::LeanObject,
    mut v_p_782_: *mut leanh::LeanObject,
    mut v_inst_783_: *mut leanh::LeanObject,
    mut v_t_784_: *mut leanh::LeanObject,
    mut v_k_785_: *mut leanh::LeanObject,
    mut v_f_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_787_ = leanh::lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_787_, 0, v_f_786_);
    v___x_788_ = leanh::lean_box(0);
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
    mut v_p_790_: *mut leanh::LeanObject,
    mut v_inst_791_: *mut leanh::LeanObject,
    mut v_t_792_: *mut leanh::LeanObject,
    mut v_f_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_794_ = leanh::lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_794_, 0, v_f_793_);
    v___x_795_ = leanh::lean_box(0);
    v___x_796_ = leanh::lean_box(0);
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
    mut v_m_798_: *mut leanh::LeanObject,
    mut v_00_u03b1_799_: *mut leanh::LeanObject,
    mut v_00_u03b2_800_: *mut leanh::LeanObject,
    mut v_p_801_: *mut leanh::LeanObject,
    mut v_inst_802_: *mut leanh::LeanObject,
    mut v_t_803_: *mut leanh::LeanObject,
    mut v_f_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_805_ = leanh::lean_alloc_closure(
        l_Lean_PrefixTree_forMatchingM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_805_, 0, v_f_804_);
    v___x_806_ = leanh::lean_box(0);
    v___x_807_ = leanh::lean_box(0);
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
pub unsafe fn runtime_initialize_Lean_Data_PrefixTree(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_PrefixTree(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_PrefixTree(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PrefixTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_PrefixTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_PrefixTree(builtin);
}