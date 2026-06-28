// Lean compiler output
// Module: Init.Data.Slice.List.Iterator
// Imports: Init.Data.Slice.List.Basic Init.Data.Iterators.Producers.List Init.Data.Iterators.Combinators.Take Init.Data.Range.Polymorphic.Basic Init.Data.Slice.Operations Init.Data.ToString.Extra
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
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_ListSlice_instToIterator___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ListSlice_instToIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ListSlice_instToIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ListSlice_instToIterator___closed__0_value) as *mut LeanObject;
pub static l_instSliceSizeListSliceData___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instSliceSizeListSliceData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceSizeListSliceData___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__0_value) as *mut LeanObject;
pub static l_instSliceSizeListSliceData___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_instSliceSizeListSliceData___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_instSliceSizeListSliceData___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instSliceSizeListSliceData___closed__1_value) as *mut LeanObject;
pub static l_List_instAppendListSlice___lam__2___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_List_instAppendListSlice___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___lam__2___closed__0_value) as *mut LeanObject;
pub static l_List_instAppendListSlice___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instAppendListSlice___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_List_instAppendListSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value) as *mut LeanObject;
pub static l_List_instAppendListSlice___closed__1_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_instAppendListSlice___lam__2 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_List_instAppendListSlice___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_List_instAppendListSlice___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_instAppendListSlice___closed__1_value) as *mut LeanObject;
pub static l_List_ListSlice_repr___redArg___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_List_ListSlice_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_ListSlice_repr___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_List_ListSlice_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_ListSlice_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_instToStringListSlice___redArg___lam__1___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_List_instToStringListSlice___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_instToStringListSlice___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_ListSlice_instToIterator___lam__0(
    mut v_x_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_346_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_351_: u8 = 0;
    let mut v_unused_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_356_: u8 = 0;
    let mut v_val_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_363_: u8 = 0;
    let mut v_unused_364_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_342_ = lean_ctor_get(v_x_341_, 1);
                if lean_obj_tag(v_stop_342_) == 0 {
                    v_list_343_ = lean_ctor_get(v_x_341_, 0);
                    v_isSharedCheck_351_ = (!lean_is_exclusive(v_x_341_)) as u8;
                    if v_isSharedCheck_351_ == 0 {
                        v_unused_352_ = lean_ctor_get(v_x_341_, 1);
                        lean_dec(v_unused_352_);
                        v___x_345_ = v_x_341_;
                        v_isShared_346_ = v_isSharedCheck_351_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_list_343_);
                        lean_dec(v_x_341_);
                        v___x_345_ = lean_box(0);
                        v_isShared_346_ = v_isSharedCheck_351_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_stop_342_);
                    v_list_353_ = lean_ctor_get(v_x_341_, 0);
                    v_isSharedCheck_363_ = (!lean_is_exclusive(v_x_341_)) as u8;
                    if v_isSharedCheck_363_ == 0 {
                        v_unused_364_ = lean_ctor_get(v_x_341_, 1);
                        lean_dec(v_unused_364_);
                        v___x_355_ = v_x_341_;
                        v_isShared_356_ = v_isSharedCheck_363_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_list_353_);
                        lean_dec(v_x_341_);
                        v___x_355_ = lean_box(0);
                        v_isShared_356_ = v_isSharedCheck_363_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_347_ = lean_unsigned_to_nat(0);
                if v_isShared_346_ == 0 {
                    lean_ctor_set(v___x_345_, 1, v_list_343_);
                    lean_ctor_set(v___x_345_, 0, v___x_347_);
                    v___x_349_ = v___x_345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
                    lean_ctor_set(v_reuseFailAlloc_350_, 1, v_list_343_);
                    v___x_349_ = v_reuseFailAlloc_350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_349_;
            }
            3 => {
                v_val_357_ = lean_ctor_get(v_stop_342_, 0);
                lean_inc(v_val_357_);
                lean_dec_ref_known(v_stop_342_, 1);
                v___x_358_ = lean_unsigned_to_nat(1);
                v___x_359_ = lean_nat_add(v_val_357_, v___x_358_);
                lean_dec(v_val_357_);
                if v_isShared_356_ == 0 {
                    lean_ctor_set(v___x_355_, 1, v_list_353_);
                    lean_ctor_set(v___x_355_, 0, v___x_359_);
                    v___x_361_ = v___x_355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
                    lean_ctor_set(v_reuseFailAlloc_362_, 1, v_list_353_);
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
pub unsafe fn l_ListSlice_instToIterator(mut v_00_u03b1_366_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_367_: *mut LeanObject = core::ptr::null_mut();
    v___f_367_ = l_ListSlice_instToIterator___closed__0;
    return v___f_367_;
}
pub unsafe fn l_instSliceSizeListSliceData___lam__0(
    mut v_it_368_: *mut LeanObject,
    mut v_acc_369_: *mut LeanObject,
    mut v_hP_370_: *mut LeanObject,
    mut v_recur_371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_376_: u8 = 0;
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut v_tail_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_372_ = lean_ctor_get(v_it_368_, 0);
                v_inner_373_ = lean_ctor_get(v_it_368_, 1);
                v_isSharedCheck_386_ = (!lean_is_exclusive(v_it_368_)) as u8;
                if v_isSharedCheck_386_ == 0 {
                    v___x_375_ = v_it_368_;
                    v_isShared_376_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inner_373_);
                    lean_inc(v_countdown_372_);
                    lean_dec(v_it_368_);
                    v___x_375_ = lean_box(0);
                    v_isShared_376_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_377_ = lean_unsigned_to_nat(1);
                v___x_378_ = lean_nat_dec_eq(v_countdown_372_, v___x_377_);
                if v___x_378_ == 0 {
                    if lean_obj_tag(v_inner_373_) == 0 {
                        lean_del_object(v___x_375_);
                        lean_dec(v_countdown_372_);
                        lean_dec_ref(v_recur_371_);
                        lean_inc(v_acc_369_);
                        return v_acc_369_;
                    } else {
                        v_tail_379_ = lean_ctor_get(v_inner_373_, 1);
                        lean_inc(v_tail_379_);
                        lean_dec_ref_known(v_inner_373_, 2);
                        v___x_380_ = lean_nat_sub(v_countdown_372_, v___x_377_);
                        lean_dec(v_countdown_372_);
                        if v_isShared_376_ == 0 {
                            lean_ctor_set(v___x_375_, 1, v_tail_379_);
                            lean_ctor_set(v___x_375_, 0, v___x_380_);
                            v___x_382_ = v___x_375_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_380_);
                            lean_ctor_set(v_reuseFailAlloc_385_, 1, v_tail_379_);
                            v___x_382_ = v_reuseFailAlloc_385_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_375_);
                    lean_dec(v_inner_373_);
                    lean_dec(v_countdown_372_);
                    lean_dec_ref(v_recur_371_);
                    lean_inc(v_acc_369_);
                    return v_acc_369_;
                }
            }
            2 => {
                v___x_383_ = lean_nat_add(v_acc_369_, v___x_377_);
                v___x_384_ = lean_apply_4(
                    v_recur_371_,
                    v___x_382_,
                    v___x_383_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceSizeListSliceData___lam__0___boxed(
    mut v_it_387_: *mut LeanObject,
    mut v_acc_388_: *mut LeanObject,
    mut v_hP_389_: *mut LeanObject,
    mut v_recur_390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_391_: *mut LeanObject = core::ptr::null_mut();
    v_res_391_ =
        l_instSliceSizeListSliceData___lam__0(v_it_387_, v_acc_388_, v_hP_389_, v_recur_390_);
    lean_dec(v_acc_388_);
    return v_res_391_;
}
pub unsafe fn l_instSliceSizeListSliceData___lam__1(
    mut v___f_392_: *mut LeanObject,
    mut v_s_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_402_: u8 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut v_unused_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v_val_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v_unused_420_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_398_ = lean_ctor_get(v_s_393_, 1);
                if lean_obj_tag(v_stop_398_) == 0 {
                    v_list_399_ = lean_ctor_get(v_s_393_, 0);
                    v_isSharedCheck_407_ = (!lean_is_exclusive(v_s_393_)) as u8;
                    if v_isSharedCheck_407_ == 0 {
                        v_unused_408_ = lean_ctor_get(v_s_393_, 1);
                        lean_dec(v_unused_408_);
                        v___x_401_ = v_s_393_;
                        v_isShared_402_ = v_isSharedCheck_407_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_list_399_);
                        lean_dec(v_s_393_);
                        v___x_401_ = lean_box(0);
                        v_isShared_402_ = v_isSharedCheck_407_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_stop_398_);
                    v_list_409_ = lean_ctor_get(v_s_393_, 0);
                    v_isSharedCheck_419_ = (!lean_is_exclusive(v_s_393_)) as u8;
                    if v_isSharedCheck_419_ == 0 {
                        v_unused_420_ = lean_ctor_get(v_s_393_, 1);
                        lean_dec(v_unused_420_);
                        v___x_411_ = v_s_393_;
                        v_isShared_412_ = v_isSharedCheck_419_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_list_409_);
                        lean_dec(v_s_393_);
                        v___x_411_ = lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_419_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_396_ = lean_unsigned_to_nat(0);
                v___x_397_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_392_,
                    v___y_395_,
                    v___x_396_,
                    lean_box(0),
                );
                return v___x_397_;
            }
            2 => {
                v___x_403_ = lean_unsigned_to_nat(0);
                if v_isShared_402_ == 0 {
                    lean_ctor_set(v___x_401_, 1, v_list_399_);
                    lean_ctor_set(v___x_401_, 0, v___x_403_);
                    v___x_405_ = v___x_401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
                    lean_ctor_set(v_reuseFailAlloc_406_, 1, v_list_399_);
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
                v_val_413_ = lean_ctor_get(v_stop_398_, 0);
                lean_inc(v_val_413_);
                lean_dec_ref_known(v_stop_398_, 1);
                v___x_414_ = lean_unsigned_to_nat(1);
                v___x_415_ = lean_nat_add(v_val_413_, v___x_414_);
                lean_dec(v_val_413_);
                if v_isShared_412_ == 0 {
                    lean_ctor_set(v___x_411_, 1, v_list_409_);
                    lean_ctor_set(v___x_411_, 0, v___x_415_);
                    v___x_417_ = v___x_411_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
                    lean_ctor_set(v_reuseFailAlloc_418_, 1, v_list_409_);
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
    mut v_00_u03b1_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_425_: *mut LeanObject = core::ptr::null_mut();
    v___f_425_ = l_instSliceSizeListSliceData___closed__1;
    return v___f_425_;
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__0(
    mut v_toPure_426_: *mut LeanObject,
    mut v_____do__lift_427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    v___x_428_ = lean_apply_2(v_toPure_426_, lean_box(0), v_____do__lift_427_);
    return v___x_428_;
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__1(
    mut v_toPure_429_: *mut LeanObject,
    mut v_recur_430_: *mut LeanObject,
    mut v___x_431_: *mut LeanObject,
    mut v_____do__lift_432_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_432_) == 0 {
        let mut v_a_433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_431_);
        lean_dec(v_recur_430_);
        v_a_433_ = lean_ctor_get(v_____do__lift_432_, 0);
        lean_inc(v_a_433_);
        lean_dec_ref_known(v_____do__lift_432_, 1);
        v___x_434_ = lean_apply_2(v_toPure_429_, lean_box(0), v_a_433_);
        return v___x_434_;
    } else {
        let mut v_a_435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_429_);
        v_a_435_ = lean_ctor_get(v_____do__lift_432_, 0);
        lean_inc(v_a_435_);
        lean_dec_ref_known(v_____do__lift_432_, 1);
        v___x_436_ = lean_apply_4(v_recur_430_, v___x_431_, v_a_435_, lean_box(0), lean_box(0));
        return v___x_436_;
    }
}
pub unsafe fn l_instForInListSliceOfMonad___redArg___lam__2(
    mut v_toPure_437_: *mut LeanObject,
    mut v_f_438_: *mut LeanObject,
    mut v_toBind_439_: *mut LeanObject,
    mut v___f_440_: *mut LeanObject,
    mut v_it_441_: *mut LeanObject,
    mut v_acc_442_: *mut LeanObject,
    mut v_hP_443_: *mut LeanObject,
    mut v_recur_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_449_: u8 = 0;
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_445_ = lean_ctor_get(v_it_441_, 0);
                v_inner_446_ = lean_ctor_get(v_it_441_, 1);
                v_isSharedCheck_464_ = (!lean_is_exclusive(v_it_441_)) as u8;
                if v_isSharedCheck_464_ == 0 {
                    v___x_448_ = v_it_441_;
                    v_isShared_449_ = v_isSharedCheck_464_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inner_446_);
                    lean_inc(v_countdown_445_);
                    lean_dec(v_it_441_);
                    v___x_448_ = lean_box(0);
                    v_isShared_449_ = v_isSharedCheck_464_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_450_ = lean_unsigned_to_nat(1);
                v___x_451_ = lean_nat_dec_eq(v_countdown_445_, v___x_450_);
                if v___x_451_ == 0 {
                    if lean_obj_tag(v_inner_446_) == 0 {
                        lean_del_object(v___x_448_);
                        lean_dec(v_countdown_445_);
                        lean_dec(v_recur_444_);
                        lean_dec(v___f_440_);
                        lean_dec(v_toBind_439_);
                        lean_dec(v_f_438_);
                        v___x_452_ = lean_apply_2(v_toPure_437_, lean_box(0), v_acc_442_);
                        return v___x_452_;
                    } else {
                        v_head_453_ = lean_ctor_get(v_inner_446_, 0);
                        lean_inc(v_head_453_);
                        v_tail_454_ = lean_ctor_get(v_inner_446_, 1);
                        lean_inc(v_tail_454_);
                        lean_dec_ref_known(v_inner_446_, 2);
                        v___x_455_ = lean_nat_sub(v_countdown_445_, v___x_450_);
                        lean_dec(v_countdown_445_);
                        if v_isShared_449_ == 0 {
                            lean_ctor_set(v___x_448_, 1, v_tail_454_);
                            lean_ctor_set(v___x_448_, 0, v___x_455_);
                            v___x_457_ = v___x_448_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_455_);
                            lean_ctor_set(v_reuseFailAlloc_462_, 1, v_tail_454_);
                            v___x_457_ = v_reuseFailAlloc_462_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_448_);
                    lean_dec(v_inner_446_);
                    lean_dec(v_countdown_445_);
                    lean_dec(v_recur_444_);
                    lean_dec(v___f_440_);
                    lean_dec(v_toBind_439_);
                    lean_dec(v_f_438_);
                    v___x_463_ = lean_apply_2(v_toPure_437_, lean_box(0), v_acc_442_);
                    return v___x_463_;
                }
            }
            2 => {
                v___f_458_ = lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_458_, 0, v_toPure_437_);
                lean_closure_set(v___f_458_, 1, v_recur_444_);
                lean_closure_set(v___f_458_, 2, v___x_457_);
                v___x_459_ = lean_apply_2(v_f_438_, v_head_453_, v_acc_442_);
                lean_inc(v_toBind_439_);
                v___x_460_ = lean_apply_4(
                    v_toBind_439_,
                    lean_box(0),
                    lean_box(0),
                    v___x_459_,
                    v___f_440_,
                );
                v___x_461_ = lean_apply_4(
                    v_toBind_439_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_465_: *mut LeanObject,
    mut v_00_u03b2_466_: *mut LeanObject,
    mut v_xs_467_: *mut LeanObject,
    mut v_init_468_: *mut LeanObject,
    mut v_f_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v_unused_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_val_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_499_: u8 = 0;
    let mut v_unused_500_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_478_ = lean_ctor_get(v_xs_467_, 1);
                if lean_obj_tag(v_stop_478_) == 0 {
                    v_list_479_ = lean_ctor_get(v_xs_467_, 0);
                    v_isSharedCheck_487_ = (!lean_is_exclusive(v_xs_467_)) as u8;
                    if v_isSharedCheck_487_ == 0 {
                        v_unused_488_ = lean_ctor_get(v_xs_467_, 1);
                        lean_dec(v_unused_488_);
                        v___x_481_ = v_xs_467_;
                        v_isShared_482_ = v_isSharedCheck_487_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_list_479_);
                        lean_dec(v_xs_467_);
                        v___x_481_ = lean_box(0);
                        v_isShared_482_ = v_isSharedCheck_487_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_stop_478_);
                    v_list_489_ = lean_ctor_get(v_xs_467_, 0);
                    v_isSharedCheck_499_ = (!lean_is_exclusive(v_xs_467_)) as u8;
                    if v_isSharedCheck_499_ == 0 {
                        v_unused_500_ = lean_ctor_get(v_xs_467_, 1);
                        lean_dec(v_unused_500_);
                        v___x_491_ = v_xs_467_;
                        v_isShared_492_ = v_isSharedCheck_499_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_list_489_);
                        lean_dec(v_xs_467_);
                        v___x_491_ = lean_box(0);
                        v_isShared_492_ = v_isSharedCheck_499_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_toApplicative_472_ = lean_ctor_get(v_inst_465_, 0);
                lean_inc_ref(v_toApplicative_472_);
                v_toBind_473_ = lean_ctor_get(v_inst_465_, 1);
                lean_inc(v_toBind_473_);
                lean_dec_ref(v_inst_465_);
                v_toPure_474_ = lean_ctor_get(v_toApplicative_472_, 1);
                lean_inc_n(v_toPure_474_, 2);
                lean_dec_ref(v_toApplicative_472_);
                v___f_475_ = lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_475_, 0, v_toPure_474_);
                v___f_476_ = lean_alloc_closure(
                    l_instForInListSliceOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
                    8,
                    4,
                );
                lean_closure_set(v___f_476_, 0, v_toPure_474_);
                lean_closure_set(v___f_476_, 1, v_f_469_);
                lean_closure_set(v___f_476_, 2, v_toBind_473_);
                lean_closure_set(v___f_476_, 3, v___f_475_);
                v___x_477_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_476_,
                    v___y_471_,
                    v_init_468_,
                    lean_box(0),
                );
                return v___x_477_;
            }
            2 => {
                v___x_483_ = lean_unsigned_to_nat(0);
                if v_isShared_482_ == 0 {
                    lean_ctor_set(v___x_481_, 1, v_list_479_);
                    lean_ctor_set(v___x_481_, 0, v___x_483_);
                    v___x_485_ = v___x_481_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
                    lean_ctor_set(v_reuseFailAlloc_486_, 1, v_list_479_);
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
                v_val_493_ = lean_ctor_get(v_stop_478_, 0);
                lean_inc(v_val_493_);
                lean_dec_ref_known(v_stop_478_, 1);
                v___x_494_ = lean_unsigned_to_nat(1);
                v___x_495_ = lean_nat_add(v_val_493_, v___x_494_);
                lean_dec(v_val_493_);
                if v_isShared_492_ == 0 {
                    lean_ctor_set(v___x_491_, 1, v_list_489_);
                    lean_ctor_set(v___x_491_, 0, v___x_495_);
                    v___x_497_ = v___x_491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
                    lean_ctor_set(v_reuseFailAlloc_498_, 1, v_list_489_);
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
    mut v_inst_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_502_: *mut LeanObject = core::ptr::null_mut();
    v___f_502_ = lean_alloc_closure(
        l_instForInListSliceOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_502_, 0, v_inst_501_);
    return v___f_502_;
}
pub unsafe fn l_instForInListSliceOfMonad(
    mut v_00_u03b1_503_: *mut LeanObject,
    mut v_m_504_: *mut LeanObject,
    mut v_inst_505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_506_: *mut LeanObject = core::ptr::null_mut();
    v___f_506_ = lean_alloc_closure(
        l_instForInListSliceOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_506_, 0, v_inst_505_);
    return v___f_506_;
}
pub unsafe fn l_List_instAppendListSlice___lam__0(
    mut v_it_507_: *mut LeanObject,
    mut v_acc_508_: *mut LeanObject,
    mut v_recur_509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_countdown_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inner_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u8 = 0;
    let mut v_head_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_countdown_510_ = lean_ctor_get(v_it_507_, 0);
                v_inner_511_ = lean_ctor_get(v_it_507_, 1);
                v_isSharedCheck_525_ = (!lean_is_exclusive(v_it_507_)) as u8;
                if v_isSharedCheck_525_ == 0 {
                    v___x_513_ = v_it_507_;
                    v_isShared_514_ = v_isSharedCheck_525_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inner_511_);
                    lean_inc(v_countdown_510_);
                    lean_dec(v_it_507_);
                    v___x_513_ = lean_box(0);
                    v_isShared_514_ = v_isSharedCheck_525_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_515_ = lean_unsigned_to_nat(1);
                v___x_516_ = lean_nat_dec_eq(v_countdown_510_, v___x_515_);
                if v___x_516_ == 0 {
                    if lean_obj_tag(v_inner_511_) == 0 {
                        lean_del_object(v___x_513_);
                        lean_dec(v_countdown_510_);
                        lean_dec_ref(v_recur_509_);
                        return v_acc_508_;
                    } else {
                        v_head_517_ = lean_ctor_get(v_inner_511_, 0);
                        lean_inc(v_head_517_);
                        v_tail_518_ = lean_ctor_get(v_inner_511_, 1);
                        lean_inc(v_tail_518_);
                        lean_dec_ref_known(v_inner_511_, 2);
                        v___x_519_ = lean_nat_sub(v_countdown_510_, v___x_515_);
                        lean_dec(v_countdown_510_);
                        if v_isShared_514_ == 0 {
                            lean_ctor_set(v___x_513_, 1, v_tail_518_);
                            lean_ctor_set(v___x_513_, 0, v___x_519_);
                            v___x_521_ = v___x_513_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_519_);
                            lean_ctor_set(v_reuseFailAlloc_524_, 1, v_tail_518_);
                            v___x_521_ = v_reuseFailAlloc_524_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_513_);
                    lean_dec(v_inner_511_);
                    lean_dec(v_countdown_510_);
                    lean_dec_ref(v_recur_509_);
                    return v_acc_508_;
                }
            }
            2 => {
                v___x_522_ = lean_array_push(v_acc_508_, v_head_517_);
                v___x_523_ = lean_apply_3(v_recur_509_, v___x_521_, v___x_522_, lean_box(0));
                return v___x_523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_instAppendListSlice___lam__2(
    mut v___f_528_: *mut LeanObject,
    mut v___f_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
    mut v_y_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v_stop_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_567_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_572_: u8 = 0;
    let mut v_unused_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_577_: u8 = 0;
    let mut v_val_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_584_: u8 = 0;
    let mut v_unused_585_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_563_ = lean_ctor_get(v_x_530_, 1);
                if lean_obj_tag(v_stop_563_) == 0 {
                    v_list_564_ = lean_ctor_get(v_x_530_, 0);
                    v_isSharedCheck_572_ = (!lean_is_exclusive(v_x_530_)) as u8;
                    if v_isSharedCheck_572_ == 0 {
                        v_unused_573_ = lean_ctor_get(v_x_530_, 1);
                        lean_dec(v_unused_573_);
                        v___x_566_ = v_x_530_;
                        v_isShared_567_ = v_isSharedCheck_572_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_list_564_);
                        lean_dec(v_x_530_);
                        v___x_566_ = lean_box(0);
                        v_isShared_567_ = v_isSharedCheck_572_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_stop_563_);
                    v_list_574_ = lean_ctor_get(v_x_530_, 0);
                    v_isSharedCheck_584_ = (!lean_is_exclusive(v_x_530_)) as u8;
                    if v_isSharedCheck_584_ == 0 {
                        v_unused_585_ = lean_ctor_get(v_x_530_, 1);
                        lean_dec(v_unused_585_);
                        v___x_576_ = v_x_530_;
                        v_isShared_577_ = v_isSharedCheck_584_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_list_574_);
                        lean_dec(v_x_530_);
                        v___x_576_ = lean_box(0);
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
                lean_dec(v___x_540_);
                lean_dec(v_a_539_);
                return v___x_541_;
            }
            2 => {
                v_list_544_ = lean_ctor_get(v_y_531_, 0);
                v_stop_545_ = lean_ctor_get(v_y_531_, 1);
                v_isSharedCheck_562_ = (!lean_is_exclusive(v_y_531_)) as u8;
                if v_isSharedCheck_562_ == 0 {
                    v___x_547_ = v_y_531_;
                    v_isShared_548_ = v_isSharedCheck_562_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_stop_545_);
                    lean_inc(v_list_544_);
                    lean_dec(v_y_531_);
                    v___x_547_ = lean_box(0);
                    v_isShared_548_ = v_isSharedCheck_562_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_549_ = lean_unsigned_to_nat(0);
                v___x_550_ = l_List_instAppendListSlice___lam__2___closed__0;
                v___x_551_ =
                    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
                        v___f_529_, v___y_543_, v___x_550_,
                    );
                v___x_552_ = lean_array_to_list(v___x_551_);
                if lean_obj_tag(v_stop_545_) == 0 {
                    if v_isShared_548_ == 0 {
                        lean_ctor_set(v___x_547_, 1, v_list_544_);
                        lean_ctor_set(v___x_547_, 0, v___x_549_);
                        v___x_554_ = v___x_547_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
                        lean_ctor_set(v_reuseFailAlloc_555_, 1, v_list_544_);
                        v___x_554_ = v_reuseFailAlloc_555_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_556_ = lean_ctor_get(v_stop_545_, 0);
                    lean_inc(v_val_556_);
                    lean_dec_ref_known(v_stop_545_, 1);
                    v___x_557_ = lean_unsigned_to_nat(1);
                    v___x_558_ = lean_nat_add(v_val_556_, v___x_557_);
                    lean_dec(v_val_556_);
                    if v_isShared_548_ == 0 {
                        lean_ctor_set(v___x_547_, 1, v_list_544_);
                        lean_ctor_set(v___x_547_, 0, v___x_558_);
                        v___x_560_ = v___x_547_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
                        lean_ctor_set(v_reuseFailAlloc_561_, 1, v_list_544_);
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
                v___x_568_ = lean_unsigned_to_nat(0);
                if v_isShared_567_ == 0 {
                    lean_ctor_set(v___x_566_, 1, v_list_564_);
                    lean_ctor_set(v___x_566_, 0, v___x_568_);
                    v___x_570_ = v___x_566_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
                    lean_ctor_set(v_reuseFailAlloc_571_, 1, v_list_564_);
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
                v_val_578_ = lean_ctor_get(v_stop_563_, 0);
                lean_inc(v_val_578_);
                lean_dec_ref_known(v_stop_563_, 1);
                v___x_579_ = lean_unsigned_to_nat(1);
                v___x_580_ = lean_nat_add(v_val_578_, v___x_579_);
                lean_dec(v_val_578_);
                if v_isShared_577_ == 0 {
                    lean_ctor_set(v___x_576_, 1, v_list_574_);
                    lean_ctor_set(v___x_576_, 0, v___x_580_);
                    v___x_582_ = v___x_576_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
                    lean_ctor_set(v_reuseFailAlloc_583_, 1, v_list_574_);
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
pub unsafe fn l_List_instAppendListSlice(mut v_00_u03b1_589_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_590_: *mut LeanObject = core::ptr::null_mut();
    v___f_590_ = l_List_instAppendListSlice___closed__1;
    return v___f_590_;
}
pub unsafe fn l_List_ListSlice_repr___redArg(
    mut v_inst_594_: *mut LeanObject,
    mut v_s_595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_list_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_600_: u8 = 0;
    let mut v___f_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_596_ = lean_ctor_get(v_s_595_, 0);
                v_stop_597_ = lean_ctor_get(v_s_595_, 1);
                v_isSharedCheck_622_ = (!lean_is_exclusive(v_s_595_)) as u8;
                if v_isSharedCheck_622_ == 0 {
                    v___x_599_ = v_s_595_;
                    v_isShared_600_ = v_isSharedCheck_622_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_597_);
                    lean_inc(v_list_596_);
                    lean_dec(v_s_595_);
                    v___x_599_ = lean_box(0);
                    v_isShared_600_ = v_isSharedCheck_622_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_601_ = l_List_instAppendListSlice___closed__0;
                if lean_obj_tag(v_stop_597_) == 0 {
                    v___x_616_ = lean_unsigned_to_nat(0);
                    v___x_617_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_617_, 0, v___x_616_);
                    lean_ctor_set(v___x_617_, 1, v_list_596_);
                    v___y_603_ = v___x_617_;
                    state = 2;
                    continue;
                } else {
                    v_val_618_ = lean_ctor_get(v_stop_597_, 0);
                    lean_inc(v_val_618_);
                    lean_dec_ref_known(v_stop_597_, 1);
                    v___x_619_ = lean_unsigned_to_nat(1);
                    v___x_620_ = lean_nat_add(v_val_618_, v___x_619_);
                    lean_dec(v_val_618_);
                    v___x_621_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_621_, 0, v___x_620_);
                    lean_ctor_set(v___x_621_, 1, v_list_596_);
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
                lean_inc(v___x_606_);
                v___x_607_ = l_List_repr___redArg(v_inst_594_, v___x_606_);
                v___x_608_ = l_List_ListSlice_repr___redArg___closed__1;
                if v_isShared_600_ == 0 {
                    lean_ctor_set_tag(v___x_599_, 5);
                    lean_ctor_set(v___x_599_, 1, v___x_608_);
                    lean_ctor_set(v___x_599_, 0, v___x_607_);
                    v___x_610_ = v___x_599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_607_);
                    lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_615_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_611_ = l_List_lengthTR___redArg(v___x_606_);
                lean_dec(v___x_606_);
                v___x_612_ = l_Nat_reprFast(v___x_611_);
                v___x_613_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_613_, 0, v___x_612_);
                v___x_614_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_614_, 0, v___x_610_);
                lean_ctor_set(v___x_614_, 1, v___x_613_);
                return v___x_614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_ListSlice_repr(
    mut v_00_u03b1_623_: *mut LeanObject,
    mut v_inst_624_: *mut LeanObject,
    mut v_s_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = l_List_ListSlice_repr___redArg(v_inst_624_, v_s_625_);
    return v___x_626_;
}
pub unsafe fn l_List_instReprListSlice___redArg___lam__0(
    mut v_inst_627_: *mut LeanObject,
    mut v_s_628_: *mut LeanObject,
    mut v_x_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = l_List_ListSlice_repr___redArg(v_inst_627_, v_s_628_);
    return v___x_630_;
}
pub unsafe fn l_List_instReprListSlice___redArg___lam__0___boxed(
    mut v_inst_631_: *mut LeanObject,
    mut v_s_632_: *mut LeanObject,
    mut v_x_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_634_: *mut LeanObject = core::ptr::null_mut();
    v_res_634_ = l_List_instReprListSlice___redArg___lam__0(v_inst_631_, v_s_632_, v_x_633_);
    lean_dec(v_x_633_);
    return v_res_634_;
}
pub unsafe fn l_List_instReprListSlice___redArg(
    mut v_inst_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_636_: *mut LeanObject = core::ptr::null_mut();
    v___f_636_ = lean_alloc_closure(
        l_List_instReprListSlice___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_636_, 0, v_inst_635_);
    return v___f_636_;
}
pub unsafe fn l_List_instReprListSlice(
    mut v_00_u03b1_637_: *mut LeanObject,
    mut v_inst_638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_639_: *mut LeanObject = core::ptr::null_mut();
    v___f_639_ = lean_alloc_closure(
        l_List_instReprListSlice___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_639_, 0, v_inst_638_);
    return v___f_639_;
}
pub unsafe fn l_List_instToStringListSlice___redArg___lam__1(
    mut v___f_641_: *mut LeanObject,
    mut v_inst_642_: *mut LeanObject,
    mut v_s_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_unused_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_list_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v_val_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_unused_674_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_652_ = lean_ctor_get(v_s_643_, 1);
                if lean_obj_tag(v_stop_652_) == 0 {
                    v_list_653_ = lean_ctor_get(v_s_643_, 0);
                    v_isSharedCheck_661_ = (!lean_is_exclusive(v_s_643_)) as u8;
                    if v_isSharedCheck_661_ == 0 {
                        v_unused_662_ = lean_ctor_get(v_s_643_, 1);
                        lean_dec(v_unused_662_);
                        v___x_655_ = v_s_643_;
                        v_isShared_656_ = v_isSharedCheck_661_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_list_653_);
                        lean_dec(v_s_643_);
                        v___x_655_ = lean_box(0);
                        v_isShared_656_ = v_isSharedCheck_661_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_stop_652_);
                    v_list_663_ = lean_ctor_get(v_s_643_, 0);
                    v_isSharedCheck_673_ = (!lean_is_exclusive(v_s_643_)) as u8;
                    if v_isSharedCheck_673_ == 0 {
                        v_unused_674_ = lean_ctor_get(v_s_643_, 1);
                        lean_dec(v_unused_674_);
                        v___x_665_ = v_s_643_;
                        v_isShared_666_ = v_isSharedCheck_673_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_list_663_);
                        lean_dec(v_s_643_);
                        v___x_665_ = lean_box(0);
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
                lean_dec_ref(v___x_650_);
                return v___x_651_;
            }
            2 => {
                v___x_657_ = lean_unsigned_to_nat(0);
                if v_isShared_656_ == 0 {
                    lean_ctor_set(v___x_655_, 1, v_list_653_);
                    lean_ctor_set(v___x_655_, 0, v___x_657_);
                    v___x_659_ = v___x_655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
                    lean_ctor_set(v_reuseFailAlloc_660_, 1, v_list_653_);
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
                v_val_667_ = lean_ctor_get(v_stop_652_, 0);
                lean_inc(v_val_667_);
                lean_dec_ref_known(v_stop_652_, 1);
                v___x_668_ = lean_unsigned_to_nat(1);
                v___x_669_ = lean_nat_add(v_val_667_, v___x_668_);
                lean_dec(v_val_667_);
                if v_isShared_666_ == 0 {
                    lean_ctor_set(v___x_665_, 1, v_list_663_);
                    lean_ctor_set(v___x_665_, 0, v___x_669_);
                    v___x_671_ = v___x_665_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
                    lean_ctor_set(v_reuseFailAlloc_672_, 1, v_list_663_);
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
    mut v_inst_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_677_: *mut LeanObject = core::ptr::null_mut();
    v___f_676_ = l_List_instAppendListSlice___closed__0;
    v___f_677_ = lean_alloc_closure(
        l_List_instToStringListSlice___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_677_, 0, v___f_676_);
    lean_closure_set(v___f_677_, 1, v_inst_675_);
    return v___f_677_;
}
pub unsafe fn l_List_instToStringListSlice(
    mut v_00_u03b1_678_: *mut LeanObject,
    mut v_inst_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l_List_instToStringListSlice___redArg(v_inst_679_);
    return v___x_680_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Producers_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_List_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_List_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Producers_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_Take(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Iterator(builtin);
}
