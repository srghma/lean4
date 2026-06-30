// Lean compiler output
// Module: Init.Data.Slice.List.Iterator
// Imports: Init.Data.Slice.List.Basic Init.Data.Iterators.Producers.List Init.Data.Iterators.Combinators.Take Init.Data.Range.Polymorphic.Basic Init.Data.Slice.Operations Init.Data.ToString.Extra
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
    lean_string_append,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Take::{
    initialize_Init_Data_Iterators_Combinators_Take,
    runtime_initialize_Init_Data_Iterators_Combinators_Take,
};
use crate::r#gen::Init::Data::Iterators::Producers::List::{
    initialize_Init_Data_Iterators_Producers_List,
    runtime_initialize_Init_Data_Iterators_Producers_List,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Basic::{
    initialize_Init_Data_Range_Polymorphic_Basic,
    runtime_initialize_Init_Data_Range_Polymorphic_Basic,
};
use crate::r#gen::Init::Data::Repr::{l_List_repr___redArg, l_Nat_reprFast};
use crate::r#gen::Init::Data::Slice::List::Basic::{
    initialize_Init_Data_Slice_List_Basic, l_List_toSlice___redArg,
    runtime_initialize_Init_Data_Slice_List_Basic,
};
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations, runtime_initialize_Init_Data_Slice_Operations,
};
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Prelude::l_List_lengthTR___redArg;
use crate::r#gen::Init::WFExtrinsicFix::{
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    l_WellFounded_opaqueFix_u2083___redArg,
};
pub static l_ListSlice_instToIterator___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_ListSlice_instToIterator___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ListSlice_instToIterator___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_ListSlice_instToIterator___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceSizeListSliceData___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceSizeListSliceData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceSizeListSliceData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceSizeListSliceData___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instSliceSizeListSliceData___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instSliceSizeListSliceData___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_instAppendListSlice___lam__2___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_List_instAppendListSlice___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_instAppendListSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_List_instAppendListSlice___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_List_instAppendListSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_instAppendListSlice___closed__1_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instAppendListSlice___lam__2 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_instAppendListSlice___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_ListSlice_repr___redArg___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [46, 116, 111, 83, 108, 105, 99, 101, 32, 48, 32, 0],
    };
static mut l_List_ListSlice_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_ListSlice_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_ListSlice_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_instToStringListSlice___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_List_instToStringListSlice___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_instToStringListSlice___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_ListSlice_instToIterator___lam__0(
    mut v_x_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_351_: u8 = 0;
    let mut v_unused_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_356_: u8 = 0;
    let mut v_val_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_363_: u8 = 0;
    let mut v_unused_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_342_ = leanh::lean_ctor_get(v_x_341_, 1);
                if leanh::lean_obj_tag(v_stop_342_) == 0 {
                    v_list_343_ = leanh::lean_ctor_get(v_x_341_, 0);
                    v_isSharedCheck_351_ = (!leanh::lean_is_exclusive(v_x_341_)) as u8;
                    if v_isSharedCheck_351_ == 0 {
                        v_unused_352_ = leanh::lean_ctor_get(v_x_341_, 1);
                        leanh::lean_dec(v_unused_352_);
                        v___x_345_ = v_x_341_;
                        v_isShared_346_ = v_isSharedCheck_351_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_343_);
                        leanh::lean_dec(v_x_341_);
                        v___x_345_ = leanh::lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_351_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_stop_342_);
                    v_list_353_ = leanh::lean_ctor_get(v_x_341_, 0);
                    v_isSharedCheck_363_ = (!leanh::lean_is_exclusive(v_x_341_)) as u8;
                    if v_isSharedCheck_363_ == 0 {
                        v_unused_364_ = leanh::lean_ctor_get(v_x_341_, 1);
                        leanh::lean_dec(v_unused_364_);
                        v___x_355_ = v_x_341_;
                        v_isShared_356_ = v_isSharedCheck_363_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_353_);
                        leanh::lean_dec(v_x_341_);
                        v___x_355_ = leanh::lean_box(0);
                        v_isShared_356_ = v_isSharedCheck_363_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_347_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_346_ == 0 {
                    leanh::lean_ctor_set(v___x_345_, 1, v_list_343_);
                    leanh::lean_ctor_set(v___x_345_, 0, v___x_347_);
                    v___x_349_ = v___x_345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_350_, 1, v_list_343_);
                    v___x_349_ = v_reuseFailAlloc_350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_349_;
            }
            3 => {
                v_val_357_ = leanh::lean_ctor_get(v_stop_342_, 0);
                leanh::lean_inc(v_val_357_);
                leanh::lean_dec_ref_known(v_stop_342_, 1);
                v___x_358_ = leanh::lean_unsigned_to_nat(1);
                v___x_359_ = lean_nat_add(v_val_357_, v___x_358_);
                leanh::lean_dec(v_val_357_);
                if v_isShared_356_ == 0 {
                    leanh::lean_ctor_set(v___x_355_, 1, v_list_353_);
                    leanh::lean_ctor_set(v___x_355_, 0, v___x_359_);
                    v___x_361_ = v___x_355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_362_, 1, v_list_353_);
                    v___x_361_ = v_reuseFailAlloc_362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ListSlice_instToIterator(
    mut v_00_u03b1_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_367_ = l_ListSlice_instToIterator___closed__0;
    return v___f_367_;
}
pub unsafe fn l_instSliceSizeListSliceData___lam__0(
    mut v_it_368_: *mut leanh::LeanObject,
    mut v_acc_369_: *mut leanh::LeanObject,
    mut v_hP_370_: *mut leanh::LeanObject,
    mut v_recur_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_countdown_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_376_: u8 = 0;
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut v_tail_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_372_ = leanh::lean_ctor_get(v_it_368_, 0);
                v_inner_373_ = leanh::lean_ctor_get(v_it_368_, 1);
                v_isSharedCheck_386_ = (!leanh::lean_is_exclusive(v_it_368_)) as u8;
                if v_isSharedCheck_386_ == 0 {
                    v___x_375_ = v_it_368_;
                    v_isShared_376_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inner_373_);
                    leanh::lean_inc(v_countdown_372_);
                    leanh::lean_dec(v_it_368_);
                    v___x_375_ = leanh::lean_box(0);
                    v_isShared_376_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_377_ = leanh::lean_unsigned_to_nat(1);
                v___x_378_ = lean_nat_dec_eq(v_countdown_372_, v___x_377_);
                if v___x_378_ == 0 {
                    if leanh::lean_obj_tag(v_inner_373_) == 0 {
                        leanh::lean_del_object(v___x_375_);
                        leanh::lean_dec(v_countdown_372_);
                        leanh::lean_dec_ref(v_recur_371_);
                        leanh::lean_inc(v_acc_369_);
                        return v_acc_369_;
                    } else {
                        v_tail_379_ = leanh::lean_ctor_get(v_inner_373_, 1);
                        leanh::lean_inc(v_tail_379_);
                        leanh::lean_dec_ref_known(v_inner_373_, 2);
                        v___x_380_ = lean_nat_sub(v_countdown_372_, v___x_377_);
                        leanh::lean_dec(v_countdown_372_);
                        if v_isShared_376_ == 0 {
                            leanh::lean_ctor_set(v___x_375_, 1, v_tail_379_);
                            leanh::lean_ctor_set(v___x_375_, 0, v___x_380_);
                            v___x_382_ = v___x_375_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_380_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_385_, 1, v_tail_379_);
                            v___x_382_ = v_reuseFailAlloc_385_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_375_);
                    leanh::lean_dec(v_inner_373_);
                    leanh::lean_dec(v_countdown_372_);
                    leanh::lean_dec_ref(v_recur_371_);
                    leanh::lean_inc(v_acc_369_);
                    return v_acc_369_;
                }
            }
            2 => {
                v___x_383_ = lean_nat_add(v_acc_369_, v___x_377_);
                v___x_384_ = leanh::lean_apply_4(
                    v_recur_371_,
                    v___x_382_,
                    v___x_383_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceSizeListSliceData___lam__0___boxed(
    mut v_it_387_: *mut leanh::LeanObject,
    mut v_acc_388_: *mut leanh::LeanObject,
    mut v_hP_389_: *mut leanh::LeanObject,
    mut v_recur_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_391_ =
        l_instSliceSizeListSliceData___lam__0(v_it_387_, v_acc_388_, v_hP_389_, v_recur_390_);
    leanh::lean_dec(v_acc_388_);
    return v_res_391_;
}
pub unsafe fn l_instSliceSizeListSliceData___lam__1(
    mut v___f_392_: *mut leanh::LeanObject,
    mut v_s_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_402_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut v_unused_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v_val_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v_unused_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_398_ = leanh::lean_ctor_get(v_s_393_, 1);
                if leanh::lean_obj_tag(v_stop_398_) == 0 {
                    v_list_399_ = leanh::lean_ctor_get(v_s_393_, 0);
                    v_isSharedCheck_407_ = (!leanh::lean_is_exclusive(v_s_393_)) as u8;
                    if v_isSharedCheck_407_ == 0 {
                        v_unused_408_ = leanh::lean_ctor_get(v_s_393_, 1);
                        leanh::lean_dec(v_unused_408_);
                        v___x_401_ = v_s_393_;
                        v_isShared_402_ = v_isSharedCheck_407_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_399_);
                        leanh::lean_dec(v_s_393_);
                        v___x_401_ = leanh::lean_box(0);
                        v_isShared_402_ = v_isSharedCheck_407_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_stop_398_);
                    v_list_409_ = leanh::lean_ctor_get(v_s_393_, 0);
                    v_isSharedCheck_419_ = (!leanh::lean_is_exclusive(v_s_393_)) as u8;
                    if v_isSharedCheck_419_ == 0 {
                        v_unused_420_ = leanh::lean_ctor_get(v_s_393_, 1);
                        leanh::lean_dec(v_unused_420_);
                        v___x_411_ = v_s_393_;
                        v_isShared_412_ = v_isSharedCheck_419_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_409_);
                        leanh::lean_dec(v_s_393_);
                        v___x_411_ = leanh::lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_419_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_396_ = leanh::lean_unsigned_to_nat(0);
                v___x_397_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_392_,
                    v___y_395_,
                    v___x_396_,
                    leanh::lean_box(0),
                );
                return v___x_397_;
            }
            2 => {
                v___x_403_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_402_ == 0 {
                    leanh::lean_ctor_set(v___x_401_, 1, v_list_399_);
                    leanh::lean_ctor_set(v___x_401_, 0, v___x_403_);
                    v___x_405_ = v___x_401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_406_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_406_, 1, v_list_399_);
                    v___x_405_ = v_reuseFailAlloc_406_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_395_ = v___x_405_;
                state = 1;
                continue;
            }
            4 => {
                v_val_413_ = leanh::lean_ctor_get(v_stop_398_, 0);
                leanh::lean_inc(v_val_413_);
                leanh::lean_dec_ref_known(v_stop_398_, 1);
                v___x_414_ = leanh::lean_unsigned_to_nat(1);
                v___x_415_ = lean_nat_add(v_val_413_, v___x_414_);
                leanh::lean_dec(v_val_413_);
                if v_isShared_412_ == 0 {
                    leanh::lean_ctor_set(v___x_411_, 1, v_list_409_);
                    leanh::lean_ctor_set(v___x_411_, 0, v___x_415_);
                    v___x_417_ = v___x_411_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_418_, 1, v_list_409_);
                    v___x_417_ = v_reuseFailAlloc_418_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_395_ = v___x_417_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceSizeListSliceData(
    mut v_00_u03b1_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_425_ = l_instSliceSizeListSliceData___closed__1;
    return v___f_425_;
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__0(
    mut v_toPure_426_: *mut leanh::LeanObject,
    mut v_____do__lift_427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_428_ = leanh::lean_apply_2(
        v_toPure_426_,
        leanh::lean_box(0),
        v_____do__lift_427_,
    );
    return v___x_428_;
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__1(
    mut v_toPure_429_: *mut leanh::LeanObject,
    mut v_recur_430_: *mut leanh::LeanObject,
    mut v___x_431_: *mut leanh::LeanObject,
    mut v_____do__lift_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_432_) == 0 {
        let mut v_a_433_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_431_);
        leanh::lean_dec(v_recur_430_);
        v_a_433_ = leanh::lean_ctor_get(v_____do__lift_432_, 0);
        leanh::lean_inc(v_a_433_);
        leanh::lean_dec_ref_known(v_____do__lift_432_, 1);
        v___x_434_ = leanh::lean_apply_2(v_toPure_429_, leanh::lean_box(0), v_a_433_);
        return v___x_434_;
    } else {
        let mut v_a_435_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_429_);
        v_a_435_ = leanh::lean_ctor_get(v_____do__lift_432_, 0);
        leanh::lean_inc(v_a_435_);
        leanh::lean_dec_ref_known(v_____do__lift_432_, 1);
        v___x_436_ = leanh::lean_apply_4(
            v_recur_430_,
            v___x_431_,
            v_a_435_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_436_;
    }
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__2(
    mut v_toPure_437_: *mut leanh::LeanObject,
    mut v_f_438_: *mut leanh::LeanObject,
    mut v_toBind_439_: *mut leanh::LeanObject,
    mut v___f_440_: *mut leanh::LeanObject,
    mut v_it_441_: *mut leanh::LeanObject,
    mut v_acc_442_: *mut leanh::LeanObject,
    mut v_hP_443_: *mut leanh::LeanObject,
    mut v_recur_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_countdown_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_445_ = leanh::lean_ctor_get(v_it_441_, 0);
                v_inner_446_ = leanh::lean_ctor_get(v_it_441_, 1);
                v_isSharedCheck_464_ = (!leanh::lean_is_exclusive(v_it_441_)) as u8;
                if v_isSharedCheck_464_ == 0 {
                    v___x_448_ = v_it_441_;
                    v_isShared_449_ = v_isSharedCheck_464_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inner_446_);
                    leanh::lean_inc(v_countdown_445_);
                    leanh::lean_dec(v_it_441_);
                    v___x_448_ = leanh::lean_box(0);
                    v_isShared_449_ = v_isSharedCheck_464_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_450_ = leanh::lean_unsigned_to_nat(1);
                v___x_451_ = lean_nat_dec_eq(v_countdown_445_, v___x_450_);
                if v___x_451_ == 0 {
                    if leanh::lean_obj_tag(v_inner_446_) == 0 {
                        leanh::lean_del_object(v___x_448_);
                        leanh::lean_dec(v_countdown_445_);
                        leanh::lean_dec(v_recur_444_);
                        leanh::lean_dec(v___f_440_);
                        leanh::lean_dec(v_toBind_439_);
                        leanh::lean_dec(v_f_438_);
                        v___x_452_ = leanh::lean_apply_2(
                            v_toPure_437_,
                            leanh::lean_box(0),
                            v_acc_442_,
                        );
                        return v___x_452_;
                    } else {
                        v_head_453_ = leanh::lean_ctor_get(v_inner_446_, 0);
                        leanh::lean_inc(v_head_453_);
                        v_tail_454_ = leanh::lean_ctor_get(v_inner_446_, 1);
                        leanh::lean_inc(v_tail_454_);
                        leanh::lean_dec_ref_known(v_inner_446_, 2);
                        v___x_455_ = lean_nat_sub(v_countdown_445_, v___x_450_);
                        leanh::lean_dec(v_countdown_445_);
                        if v_isShared_449_ == 0 {
                            leanh::lean_ctor_set(v___x_448_, 1, v_tail_454_);
                            leanh::lean_ctor_set(v___x_448_, 0, v___x_455_);
                            v___x_457_ = v___x_448_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_462_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_455_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_462_, 1, v_tail_454_);
                            v___x_457_ = v_reuseFailAlloc_462_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_448_);
                    leanh::lean_dec(v_inner_446_);
                    leanh::lean_dec(v_countdown_445_);
                    leanh::lean_dec(v_recur_444_);
                    leanh::lean_dec(v___f_440_);
                    leanh::lean_dec(v_toBind_439_);
                    leanh::lean_dec(v_f_438_);
                    v___x_463_ = leanh::lean_apply_2(
                        v_toPure_437_,
                        leanh::lean_box(0),
                        v_acc_442_,
                    );
                    return v___x_463_;
                }
            }
            2 => {
                v___f_458_ = leanh::lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_458_, 0, v_toPure_437_);
                leanh::lean_closure_set(v___f_458_, 1, v_recur_444_);
                leanh::lean_closure_set(v___f_458_, 2, v___x_457_);
                v___x_459_ = leanh::lean_apply_2(v_f_438_, v_head_453_, v_acc_442_);
                leanh::lean_inc(v_toBind_439_);
                v___x_460_ = leanh::lean_apply_4(
                    v_toBind_439_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_459_,
                    v___f_440_,
                );
                v___x_461_ = leanh::lean_apply_4(
                    v_toBind_439_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_460_,
                    v___f_458_,
                );
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__3(
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_00_u03b2_466_: *mut leanh::LeanObject,
    mut v_xs_467_: *mut leanh::LeanObject,
    mut v_init_468_: *mut leanh::LeanObject,
    mut v_f_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v_unused_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_val_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_unused_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_478_ = leanh::lean_ctor_get(v_xs_467_, 1);
                if leanh::lean_obj_tag(v_stop_478_) == 0 {
                    v_list_479_ = leanh::lean_ctor_get(v_xs_467_, 0);
                    v_isSharedCheck_487_ = (!leanh::lean_is_exclusive(v_xs_467_)) as u8;
                    if v_isSharedCheck_487_ == 0 {
                        v_unused_488_ = leanh::lean_ctor_get(v_xs_467_, 1);
                        leanh::lean_dec(v_unused_488_);
                        v___x_481_ = v_xs_467_;
                        v_isShared_482_ = v_isSharedCheck_487_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_479_);
                        leanh::lean_dec(v_xs_467_);
                        v___x_481_ = leanh::lean_box(0);
                        v_isShared_482_ = v_isSharedCheck_487_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_stop_478_);
                    v_list_489_ = leanh::lean_ctor_get(v_xs_467_, 0);
                    v_isSharedCheck_499_ = (!leanh::lean_is_exclusive(v_xs_467_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v_unused_500_ = leanh::lean_ctor_get(v_xs_467_, 1);
                        leanh::lean_dec(v_unused_500_);
                        v___x_491_ = v_xs_467_;
                        v_isShared_492_ = v_isSharedCheck_499_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_489_);
                        leanh::lean_dec(v_xs_467_);
                        v___x_491_ = leanh::lean_box(0);
                        v_isShared_492_ = v_isSharedCheck_499_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_toApplicative_472_ = leanh::lean_ctor_get(v_inst_465_, 0);
                leanh::lean_inc_ref(v_toApplicative_472_);
                v_toBind_473_ = leanh::lean_ctor_get(v_inst_465_, 1);
                leanh::lean_inc(v_toBind_473_);
                leanh::lean_dec_ref(v_inst_465_);
                v_toPure_474_ = leanh::lean_ctor_get(v_toApplicative_472_, 1);
                leanh::lean_inc_n(v_toPure_474_, 2);
                leanh::lean_dec_ref(v_toApplicative_472_);
                v___f_475_ = leanh::lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_475_, 0, v_toPure_474_);
                v___f_476_ = leanh::lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    8,
                    4,
                );
                leanh::lean_closure_set(v___f_476_, 0, v_toPure_474_);
                leanh::lean_closure_set(v___f_476_, 1, v_f_469_);
                leanh::lean_closure_set(v___f_476_, 2, v_toBind_473_);
                leanh::lean_closure_set(v___f_476_, 3, v___f_475_);
                v___x_477_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_476_,
                    v___y_471_,
                    v_init_468_,
                    leanh::lean_box(0),
                );
                return v___x_477_;
            }
            2 => {
                v___x_483_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_482_ == 0 {
                    leanh::lean_ctor_set(v___x_481_, 1, v_list_479_);
                    leanh::lean_ctor_set(v___x_481_, 0, v___x_483_);
                    v___x_485_ = v___x_481_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_486_, 1, v_list_479_);
                    v___x_485_ = v_reuseFailAlloc_486_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_471_ = v___x_485_;
                state = 1;
                continue;
            }
            4 => {
                v_val_493_ = leanh::lean_ctor_get(v_stop_478_, 0);
                leanh::lean_inc(v_val_493_);
                leanh::lean_dec_ref_known(v_stop_478_, 1);
                v___x_494_ = leanh::lean_unsigned_to_nat(1);
                v___x_495_ = lean_nat_add(v_val_493_, v___x_494_);
                leanh::lean_dec(v_val_493_);
                if v_isShared_492_ == 0 {
                    leanh::lean_ctor_set(v___x_491_, 1, v_list_489_);
                    leanh::lean_ctor_set(v___x_491_, 0, v___x_495_);
                    v___x_497_ = v___x_491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_498_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_498_, 1, v_list_489_);
                    v___x_497_ = v_reuseFailAlloc_498_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_471_ = v___x_497_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instForInListSliceOfMonad___redArg(
    mut v_inst_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_502_ = leanh::lean_alloc_closure(
        l_instForInListSliceOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_502_, 0, v_inst_501_);
    return v___f_502_;
}
pub unsafe fn l_instForInListSliceOfMonad(
    mut v_00_u03b1_503_: *mut leanh::LeanObject,
    mut v_m_504_: *mut leanh::LeanObject,
    mut v_inst_505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_506_ = leanh::lean_alloc_closure(
        l_instForInListSliceOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_506_, 0, v_inst_505_);
    return v___f_506_;
}
pub unsafe fn l_List_instAppendListSlice___lam__0(
    mut v_it_507_: *mut leanh::LeanObject,
    mut v_acc_508_: *mut leanh::LeanObject,
    mut v_recur_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_countdown_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inner_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v_head_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_510_ = leanh::lean_ctor_get(v_it_507_, 0);
                v_inner_511_ = leanh::lean_ctor_get(v_it_507_, 1);
                v_isSharedCheck_525_ = (!leanh::lean_is_exclusive(v_it_507_)) as u8;
                if v_isSharedCheck_525_ == 0 {
                    v___x_513_ = v_it_507_;
                    v_isShared_514_ = v_isSharedCheck_525_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inner_511_);
                    leanh::lean_inc(v_countdown_510_);
                    leanh::lean_dec(v_it_507_);
                    v___x_513_ = leanh::lean_box(0);
                    v_isShared_514_ = v_isSharedCheck_525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_515_ = leanh::lean_unsigned_to_nat(1);
                v___x_516_ = lean_nat_dec_eq(v_countdown_510_, v___x_515_);
                if v___x_516_ == 0 {
                    if leanh::lean_obj_tag(v_inner_511_) == 0 {
                        leanh::lean_del_object(v___x_513_);
                        leanh::lean_dec(v_countdown_510_);
                        leanh::lean_dec_ref(v_recur_509_);
                        return v_acc_508_;
                    } else {
                        v_head_517_ = leanh::lean_ctor_get(v_inner_511_, 0);
                        leanh::lean_inc(v_head_517_);
                        v_tail_518_ = leanh::lean_ctor_get(v_inner_511_, 1);
                        leanh::lean_inc(v_tail_518_);
                        leanh::lean_dec_ref_known(v_inner_511_, 2);
                        v___x_519_ = lean_nat_sub(v_countdown_510_, v___x_515_);
                        leanh::lean_dec(v_countdown_510_);
                        if v_isShared_514_ == 0 {
                            leanh::lean_ctor_set(v___x_513_, 1, v_tail_518_);
                            leanh::lean_ctor_set(v___x_513_, 0, v___x_519_);
                            v___x_521_ = v___x_513_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_519_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_524_, 1, v_tail_518_);
                            v___x_521_ = v_reuseFailAlloc_524_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_513_);
                    leanh::lean_dec(v_inner_511_);
                    leanh::lean_dec(v_countdown_510_);
                    leanh::lean_dec_ref(v_recur_509_);
                    return v_acc_508_;
                }
            }
            2 => {
                v___x_522_ = lean_array_push(v_acc_508_, v_head_517_);
                v___x_523_ = leanh::lean_apply_3(
                    v_recur_509_,
                    v___x_521_,
                    v___x_522_,
                    leanh::lean_box(0),
                );
                return v___x_523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_instAppendListSlice___lam__2(
    mut v___f_528_: *mut leanh::LeanObject,
    mut v___f_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
    mut v_y_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_stop_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_567_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut v_unused_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v_val_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_584_: u8 = 0;
    let mut v_unused_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_563_ = leanh::lean_ctor_get(v_x_530_, 1);
                if leanh::lean_obj_tag(v_stop_563_) == 0 {
                    v_list_564_ = leanh::lean_ctor_get(v_x_530_, 0);
                    v_isSharedCheck_572_ = (!leanh::lean_is_exclusive(v_x_530_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v_unused_573_ = leanh::lean_ctor_get(v_x_530_, 1);
                        leanh::lean_dec(v_unused_573_);
                        v___x_566_ = v_x_530_;
                        v_isShared_567_ = v_isSharedCheck_572_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_564_);
                        leanh::lean_dec(v_x_530_);
                        v___x_566_ = leanh::lean_box(0);
                        v_isShared_567_ = v_isSharedCheck_572_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_stop_563_);
                    v_list_574_ = leanh::lean_ctor_get(v_x_530_, 0);
                    v_isSharedCheck_584_ = (!leanh::lean_is_exclusive(v_x_530_)) as u8;
                    if v_isSharedCheck_584_ == 0 {
                        v_unused_585_ = leanh::lean_ctor_get(v_x_530_, 1);
                        leanh::lean_dec(v_unused_585_);
                        v___x_576_ = v_x_530_;
                        v_isShared_577_ = v_isSharedCheck_584_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_574_);
                        leanh::lean_dec(v_x_530_);
                        v___x_576_ = leanh::lean_box(0);
                        v_isShared_577_ = v_isSharedCheck_584_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_537_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_528_, v___y_536_, v___y_534_,
                    );
                v___x_538_ = lean_array_to_list(v___x_537_);
                v_a_539_ = l_List_appendTR___redArg(v___y_535_, v___x_538_);
                v___x_540_ = l_List_lengthTR___redArg(v_a_539_);
                v___x_541_ = l_List_toSlice___redArg(v_a_539_, v___y_533_, v___x_540_);
                leanh::lean_dec(v___x_540_);
                leanh::lean_dec(v_a_539_);
                return v___x_541_;
            }
            2 => {
                v_list_544_ = leanh::lean_ctor_get(v_y_531_, 0);
                v_stop_545_ = leanh::lean_ctor_get(v_y_531_, 1);
                v_isSharedCheck_562_ = (!leanh::lean_is_exclusive(v_y_531_)) as u8;
                if v_isSharedCheck_562_ == 0 {
                    v___x_547_ = v_y_531_;
                    v_isShared_548_ = v_isSharedCheck_562_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_545_);
                    leanh::lean_inc(v_list_544_);
                    leanh::lean_dec(v_y_531_);
                    v___x_547_ = leanh::lean_box(0);
                    v_isShared_548_ = v_isSharedCheck_562_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_549_ = leanh::lean_unsigned_to_nat(0);
                v___x_550_ = l_List_instAppendListSlice___lam__2___closed__0;
                v___x_551_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_529_, v___y_543_, v___x_550_,
                    );
                v___x_552_ = lean_array_to_list(v___x_551_);
                if leanh::lean_obj_tag(v_stop_545_) == 0 {
                    if v_isShared_548_ == 0 {
                        leanh::lean_ctor_set(v___x_547_, 1, v_list_544_);
                        leanh::lean_ctor_set(v___x_547_, 0, v___x_549_);
                        v___x_554_ = v___x_547_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_555_, 1, v_list_544_);
                        v___x_554_ = v_reuseFailAlloc_555_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_556_ = leanh::lean_ctor_get(v_stop_545_, 0);
                    leanh::lean_inc(v_val_556_);
                    leanh::lean_dec_ref_known(v_stop_545_, 1);
                    v___x_557_ = leanh::lean_unsigned_to_nat(1);
                    v___x_558_ = lean_nat_add(v_val_556_, v___x_557_);
                    leanh::lean_dec(v_val_556_);
                    if v_isShared_548_ == 0 {
                        leanh::lean_ctor_set(v___x_547_, 1, v_list_544_);
                        leanh::lean_ctor_set(v___x_547_, 0, v___x_558_);
                        v___x_560_ = v___x_547_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_561_, 1, v_list_544_);
                        v___x_560_ = v_reuseFailAlloc_561_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_533_ = v___x_549_;
                v___y_534_ = v___x_550_;
                v___y_535_ = v___x_552_;
                v___y_536_ = v___x_554_;
                state = 1;
                continue;
            }
            5 => {
                v___y_533_ = v___x_549_;
                v___y_534_ = v___x_550_;
                v___y_535_ = v___x_552_;
                v___y_536_ = v___x_560_;
                state = 1;
                continue;
            }
            6 => {
                v___x_568_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_567_ == 0 {
                    leanh::lean_ctor_set(v___x_566_, 1, v_list_564_);
                    leanh::lean_ctor_set(v___x_566_, 0, v___x_568_);
                    v___x_570_ = v___x_566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_571_, 1, v_list_564_);
                    v___x_570_ = v_reuseFailAlloc_571_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_543_ = v___x_570_;
                state = 2;
                continue;
            }
            8 => {
                v_val_578_ = leanh::lean_ctor_get(v_stop_563_, 0);
                leanh::lean_inc(v_val_578_);
                leanh::lean_dec_ref_known(v_stop_563_, 1);
                v___x_579_ = leanh::lean_unsigned_to_nat(1);
                v___x_580_ = lean_nat_add(v_val_578_, v___x_579_);
                leanh::lean_dec(v_val_578_);
                if v_isShared_577_ == 0 {
                    leanh::lean_ctor_set(v___x_576_, 1, v_list_574_);
                    leanh::lean_ctor_set(v___x_576_, 0, v___x_580_);
                    v___x_582_ = v___x_576_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_583_, 1, v_list_574_);
                    v___x_582_ = v_reuseFailAlloc_583_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_543_ = v___x_582_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_instAppendListSlice(
    mut v_00_u03b1_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_590_ = l_List_instAppendListSlice___closed__1;
    return v___f_590_;
}
pub unsafe fn l_List_ListSlice_repr___redArg(
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_s_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_600_: u8 = 0;
    let mut v___f_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_596_ = leanh::lean_ctor_get(v_s_595_, 0);
                v_stop_597_ = leanh::lean_ctor_get(v_s_595_, 1);
                v_isSharedCheck_622_ = (!leanh::lean_is_exclusive(v_s_595_)) as u8;
                if v_isSharedCheck_622_ == 0 {
                    v___x_599_ = v_s_595_;
                    v_isShared_600_ = v_isSharedCheck_622_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_597_);
                    leanh::lean_inc(v_list_596_);
                    leanh::lean_dec(v_s_595_);
                    v___x_599_ = leanh::lean_box(0);
                    v_isShared_600_ = v_isSharedCheck_622_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_601_ = l_List_instAppendListSlice___closed__0;
                if leanh::lean_obj_tag(v_stop_597_) == 0 {
                    v___x_616_ = leanh::lean_unsigned_to_nat(0);
                    v___x_617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_617_, 0, v___x_616_);
                    leanh::lean_ctor_set(v___x_617_, 1, v_list_596_);
                    v___y_603_ = v___x_617_;
                    state = 2;
                    continue;
                } else {
                    v_val_618_ = leanh::lean_ctor_get(v_stop_597_, 0);
                    leanh::lean_inc(v_val_618_);
                    leanh::lean_dec_ref_known(v_stop_597_, 1);
                    v___x_619_ = leanh::lean_unsigned_to_nat(1);
                    v___x_620_ = lean_nat_add(v_val_618_, v___x_619_);
                    leanh::lean_dec(v_val_618_);
                    v___x_621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_621_, 0, v___x_620_);
                    leanh::lean_ctor_set(v___x_621_, 1, v_list_596_);
                    v___y_603_ = v___x_621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_604_ = l_List_instAppendListSlice___lam__2___closed__0;
                v___x_605_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_601_, v___y_603_, v___x_604_,
                    );
                v___x_606_ = lean_array_to_list(v___x_605_);
                leanh::lean_inc(v___x_606_);
                v___x_607_ = l_List_repr___redArg(v_inst_594_, v___x_606_);
                v___x_608_ = l_List_ListSlice_repr___redArg___closed__1;
                if v_isShared_600_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_599_, 5);
                    leanh::lean_ctor_set(v___x_599_, 1, v___x_608_);
                    leanh::lean_ctor_set(v___x_599_, 0, v___x_607_);
                    v___x_610_ = v___x_599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_615_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_611_ = l_List_lengthTR___redArg(v___x_606_);
                leanh::lean_dec(v___x_606_);
                v___x_612_ = l_Nat_reprFast(v___x_611_);
                v___x_613_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_613_, 0, v___x_612_);
                v___x_614_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_614_, 0, v___x_610_);
                leanh::lean_ctor_set(v___x_614_, 1, v___x_613_);
                return v___x_614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_ListSlice_repr(
    mut v_00_u03b1_623_: *mut leanh::LeanObject,
    mut v_inst_624_: *mut leanh::LeanObject,
    mut v_s_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = l_List_ListSlice_repr___redArg(v_inst_624_, v_s_625_);
    return v___x_626_;
}
pub unsafe fn l_List_instReprListSlice___redArg___lam__0(
    mut v_inst_627_: *mut leanh::LeanObject,
    mut v_s_628_: *mut leanh::LeanObject,
    mut v_x_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_630_ = l_List_ListSlice_repr___redArg(v_inst_627_, v_s_628_);
    return v___x_630_;
}
pub unsafe fn l_List_instReprListSlice___redArg___lam__0___boxed(
    mut v_inst_631_: *mut leanh::LeanObject,
    mut v_s_632_: *mut leanh::LeanObject,
    mut v_x_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_List_instReprListSlice___redArg___lam__0(v_inst_631_, v_s_632_, v_x_633_);
    leanh::lean_dec(v_x_633_);
    return v_res_634_;
}
pub unsafe fn l_List_instReprListSlice___redArg(
    mut v_inst_635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_636_ = leanh::lean_alloc_closure(
        l_List_instReprListSlice___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_636_, 0, v_inst_635_);
    return v___f_636_;
}
pub unsafe fn l_List_instReprListSlice(
    mut v_00_u03b1_637_: *mut leanh::LeanObject,
    mut v_inst_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_639_ = leanh::lean_alloc_closure(
        l_List_instReprListSlice___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_639_, 0, v_inst_638_);
    return v___f_639_;
}
pub unsafe fn l_List_instToStringListSlice___redArg___lam__1(
    mut v___f_641_: *mut leanh::LeanObject,
    mut v_inst_642_: *mut leanh::LeanObject,
    mut v_s_643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_unused_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_list_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v_val_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_unused_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_652_ = leanh::lean_ctor_get(v_s_643_, 1);
                if leanh::lean_obj_tag(v_stop_652_) == 0 {
                    v_list_653_ = leanh::lean_ctor_get(v_s_643_, 0);
                    v_isSharedCheck_661_ = (!leanh::lean_is_exclusive(v_s_643_)) as u8;
                    if v_isSharedCheck_661_ == 0 {
                        v_unused_662_ = leanh::lean_ctor_get(v_s_643_, 1);
                        leanh::lean_dec(v_unused_662_);
                        v___x_655_ = v_s_643_;
                        v_isShared_656_ = v_isSharedCheck_661_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_653_);
                        leanh::lean_dec(v_s_643_);
                        v___x_655_ = leanh::lean_box(0);
                        v_isShared_656_ = v_isSharedCheck_661_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_stop_652_);
                    v_list_663_ = leanh::lean_ctor_get(v_s_643_, 0);
                    v_isSharedCheck_673_ = (!leanh::lean_is_exclusive(v_s_643_)) as u8;
                    if v_isSharedCheck_673_ == 0 {
                        v_unused_674_ = leanh::lean_ctor_get(v_s_643_, 1);
                        leanh::lean_dec(v_unused_674_);
                        v___x_665_ = v_s_643_;
                        v_isShared_666_ = v_isSharedCheck_673_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_list_663_);
                        leanh::lean_dec(v_s_643_);
                        v___x_665_ = leanh::lean_box(0);
                        v_isShared_666_ = v_isSharedCheck_673_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_646_ = l_List_instAppendListSlice___lam__2___closed__0;
                v___x_647_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_641_, v___y_645_, v___x_646_,
                    );
                v___x_648_ = l_List_instToStringListSlice___redArg___lam__1___closed__0;
                v___x_649_ = lean_array_to_list(v___x_647_);
                v___x_650_ = l_List_toString___redArg(v_inst_642_, v___x_649_);
                v___x_651_ = lean_string_append(v___x_648_, v___x_650_);
                leanh::lean_dec_ref(v___x_650_);
                return v___x_651_;
            }
            2 => {
                v___x_657_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_656_ == 0 {
                    leanh::lean_ctor_set(v___x_655_, 1, v_list_653_);
                    leanh::lean_ctor_set(v___x_655_, 0, v___x_657_);
                    v___x_659_ = v___x_655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_660_, 1, v_list_653_);
                    v___x_659_ = v_reuseFailAlloc_660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_645_ = v___x_659_;
                state = 1;
                continue;
            }
            4 => {
                v_val_667_ = leanh::lean_ctor_get(v_stop_652_, 0);
                leanh::lean_inc(v_val_667_);
                leanh::lean_dec_ref_known(v_stop_652_, 1);
                v___x_668_ = leanh::lean_unsigned_to_nat(1);
                v___x_669_ = lean_nat_add(v_val_667_, v___x_668_);
                leanh::lean_dec(v_val_667_);
                if v_isShared_666_ == 0 {
                    leanh::lean_ctor_set(v___x_665_, 1, v_list_663_);
                    leanh::lean_ctor_set(v___x_665_, 0, v___x_669_);
                    v___x_671_ = v___x_665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_672_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_672_, 1, v_list_663_);
                    v___x_671_ = v_reuseFailAlloc_672_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_645_ = v___x_671_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_instToStringListSlice___redArg(
    mut v_inst_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_676_ = l_List_instAppendListSlice___closed__0;
    v___f_677_ = leanh::lean_alloc_closure(
        l_List_instToStringListSlice___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_677_, 0, v___f_676_);
    leanh::lean_closure_set(v___f_677_, 1, v_inst_675_);
    return v___f_677_;
}
pub unsafe fn l_List_instToStringListSlice(
    mut v_00_u03b1_678_: *mut leanh::LeanObject,
    mut v_inst_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_List_instToStringListSlice___redArg(v_inst_679_);
    return v___x_680_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_List_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Producers_List(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Iterator(builtin);
}