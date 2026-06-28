// Lean compiler output
// Module: Init.Data.Slice.Array.Iterator
// Imports: Init.Data.Slice.Operations Init.Data.Range.Polymorphic.Basic Init.Omega Init.Data.Array.Subarray Init.Data.ToString.Extra
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_repr___redArg};
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, l_Array_toSubarray___redArg,
    runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Basic::{
    initialize_Init_Data_Range_Polymorphic_Basic,
    runtime_initialize_Init_Data_Range_Polymorphic_Basic,
};
use crate::r#gen::Init::Data::Slice::Operations::{
    initialize_Init_Data_Slice_Operations,
    l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg,
    runtime_initialize_Init_Data_Slice_Operations,
};
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::{
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    l_WellFounded_opaqueFix_u2083___redArg,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_instIteratorSubarrayIteratorId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instIteratorSubarrayIteratorId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instIteratorSubarrayIteratorId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instIteratorSubarrayIteratorId___closed__0_value) as *mut LeanObject;
pub static l_Subarray_instToIterator___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Subarray_instToIterator___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Subarray_instToIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Subarray_instToIterator___closed__0_value) as *mut LeanObject;
pub static l_Subarray_copy___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Subarray_copy___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Subarray_copy___redArg___closed__0_value) as *mut LeanObject;
pub static l_instCoeSubarrayArray___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Subarray_copy as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instCoeSubarrayArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instCoeSubarrayArray___closed__0_value) as *mut LeanObject;
pub static l_Array_instAppendSubarray___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instAppendSubarray___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_instAppendSubarray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value) as *mut LeanObject;
pub static l_Array_instAppendSubarray___closed__1_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Array_instAppendSubarray___lam__2 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_instAppendSubarray___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instAppendSubarray___closed__1_value) as *mut LeanObject;
pub static l_Array_Subarray_repr___redArg___closed__0_value: LeanStringObject<12> =
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
        m_data: [46, 116, 111, 83, 117, 98, 97, 114, 114, 97, 121, 0],
    };
static mut l_Array_Subarray_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_Subarray_repr___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_Subarray_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_instToStringSubarray___redArg___lam__1___closed__0_value: LeanStringObject<2> =
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
static mut l_Array_instToStringSubarray___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_instToStringSubarray___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_SubarrayIterator_step___redArg(mut v_x_329_: *mut LeanObject) -> *mut LeanObject {
    let mut v_array_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_335_: u8 = 0;
    let mut v___x_336_: u8 = 0;
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_330_ = lean_ctor_get(v_x_329_, 0);
                v_start_331_ = lean_ctor_get(v_x_329_, 1);
                v_stop_332_ = lean_ctor_get(v_x_329_, 2);
                v_isSharedCheck_345_ = (!lean_is_exclusive(v_x_329_)) as u8;
                if v_isSharedCheck_345_ == 0 {
                    v___x_334_ = v_x_329_;
                    v_isShared_335_ = v_isSharedCheck_345_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_332_);
                    lean_inc(v_start_331_);
                    lean_inc(v_array_330_);
                    lean_dec(v_x_329_);
                    v___x_334_ = lean_box(0);
                    v_isShared_335_ = v_isSharedCheck_345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_336_ = lean_nat_dec_lt(v_start_331_, v_stop_332_);
                if v___x_336_ == 0 {
                    lean_del_object(v___x_334_);
                    lean_dec(v_stop_332_);
                    lean_dec(v_start_331_);
                    lean_dec_ref(v_array_330_);
                    v___x_337_ = lean_box(2);
                    return v___x_337_;
                } else {
                    v___x_338_ = lean_unsigned_to_nat(1);
                    v___x_339_ = lean_nat_add(v_start_331_, v___x_338_);
                    lean_inc_ref(v_array_330_);
                    if v_isShared_335_ == 0 {
                        lean_ctor_set(v___x_334_, 1, v___x_339_);
                        v___x_341_ = v___x_334_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_344_, 0, v_array_330_);
                        lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_339_);
                        lean_ctor_set(v_reuseFailAlloc_344_, 2, v_stop_332_);
                        v___x_341_ = v_reuseFailAlloc_344_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_342_ = lean_array_fget(v_array_330_, v_start_331_);
                lean_dec(v_start_331_);
                lean_dec_ref(v_array_330_);
                v___x_343_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_343_, 0, v___x_341_);
                lean_ctor_set(v___x_343_, 1, v___x_342_);
                return v___x_343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_SubarrayIterator_step(
    mut v_00_u03b1_346_: *mut LeanObject,
    mut v_m_347_: *mut LeanObject,
    mut v_x_348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_354_: u8 = 0;
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_349_ = lean_ctor_get(v_x_348_, 0);
                v_start_350_ = lean_ctor_get(v_x_348_, 1);
                v_stop_351_ = lean_ctor_get(v_x_348_, 2);
                v_isSharedCheck_364_ = (!lean_is_exclusive(v_x_348_)) as u8;
                if v_isSharedCheck_364_ == 0 {
                    v___x_353_ = v_x_348_;
                    v_isShared_354_ = v_isSharedCheck_364_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_351_);
                    lean_inc(v_start_350_);
                    lean_inc(v_array_349_);
                    lean_dec(v_x_348_);
                    v___x_353_ = lean_box(0);
                    v_isShared_354_ = v_isSharedCheck_364_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_355_ = lean_nat_dec_lt(v_start_350_, v_stop_351_);
                if v___x_355_ == 0 {
                    lean_del_object(v___x_353_);
                    lean_dec(v_stop_351_);
                    lean_dec(v_start_350_);
                    lean_dec_ref(v_array_349_);
                    v___x_356_ = lean_box(2);
                    return v___x_356_;
                } else {
                    v___x_357_ = lean_unsigned_to_nat(1);
                    v___x_358_ = lean_nat_add(v_start_350_, v___x_357_);
                    lean_inc_ref(v_array_349_);
                    if v_isShared_354_ == 0 {
                        lean_ctor_set(v___x_353_, 1, v___x_358_);
                        v___x_360_ = v___x_353_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_363_, 0, v_array_349_);
                        lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_358_);
                        lean_ctor_set(v_reuseFailAlloc_363_, 2, v_stop_351_);
                        v___x_360_ = v_reuseFailAlloc_363_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_361_ = lean_array_fget(v_array_349_, v_start_350_);
                lean_dec(v_start_350_);
                lean_dec_ref(v_array_349_);
                v___x_362_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_362_, 0, v___x_360_);
                lean_ctor_set(v___x_362_, 1, v___x_361_);
                return v___x_362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instIteratorSubarrayIteratorId___lam__0(
    mut v_it_365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_371_: u8 = 0;
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_366_ = lean_ctor_get(v_it_365_, 0);
                v_start_367_ = lean_ctor_get(v_it_365_, 1);
                v_stop_368_ = lean_ctor_get(v_it_365_, 2);
                v_isSharedCheck_381_ = (!lean_is_exclusive(v_it_365_)) as u8;
                if v_isSharedCheck_381_ == 0 {
                    v___x_370_ = v_it_365_;
                    v_isShared_371_ = v_isSharedCheck_381_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_368_);
                    lean_inc(v_start_367_);
                    lean_inc(v_array_366_);
                    lean_dec(v_it_365_);
                    v___x_370_ = lean_box(0);
                    v_isShared_371_ = v_isSharedCheck_381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_372_ = lean_nat_dec_lt(v_start_367_, v_stop_368_);
                if v___x_372_ == 0 {
                    lean_del_object(v___x_370_);
                    lean_dec(v_stop_368_);
                    lean_dec(v_start_367_);
                    lean_dec_ref(v_array_366_);
                    v___x_373_ = lean_box(2);
                    return v___x_373_;
                } else {
                    v___x_374_ = lean_unsigned_to_nat(1);
                    v___x_375_ = lean_nat_add(v_start_367_, v___x_374_);
                    lean_inc_ref(v_array_366_);
                    if v_isShared_371_ == 0 {
                        lean_ctor_set(v___x_370_, 1, v___x_375_);
                        v___x_377_ = v___x_370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_380_, 0, v_array_366_);
                        lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_375_);
                        lean_ctor_set(v_reuseFailAlloc_380_, 2, v_stop_368_);
                        v___x_377_ = v_reuseFailAlloc_380_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_378_ = lean_array_fget(v_array_366_, v_start_367_);
                lean_dec(v_start_367_);
                lean_dec_ref(v_array_366_);
                v___x_379_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_379_, 0, v___x_377_);
                lean_ctor_set(v___x_379_, 1, v___x_378_);
                return v___x_379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instIteratorSubarrayIteratorId(
    mut v_00_u03b1_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_384_: *mut LeanObject = core::ptr::null_mut();
    v___f_384_ = l_instIteratorSubarrayIteratorId___closed__0;
    return v___f_384_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(
    mut v_x_385_: *mut LeanObject,
    mut v_h__1_386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_apply_1(v_h__1_386_, v_x_385_);
    return v___x_387_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_motive_389_: *mut LeanObject,
    mut v_x_390_: *mut LeanObject,
    mut v_h__1_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    v___x_392_ = lean_apply_1(v_h__1_391_, v_x_390_);
    return v___x_392_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(
    mut v_00_u03b1_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = lean_box(0);
    return v___x_394_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(
    mut v_toPure_395_: *mut LeanObject,
    mut v_recur_396_: *mut LeanObject,
    mut v_it_397_: *mut LeanObject,
    mut v_____do__lift_398_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_398_) == 0 {
        let mut v_a_399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_397_);
        lean_dec(v_recur_396_);
        v_a_399_ = lean_ctor_get(v_____do__lift_398_, 0);
        lean_inc(v_a_399_);
        lean_dec_ref_known(v_____do__lift_398_, 1);
        v___x_400_ = lean_apply_2(v_toPure_395_, lean_box(0), v_a_399_);
        return v___x_400_;
    } else {
        let mut v_a_401_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_395_);
        v_a_401_ = lean_ctor_get(v_____do__lift_398_, 0);
        lean_inc(v_a_401_);
        lean_dec_ref_known(v_____do__lift_398_, 1);
        v___x_402_ = lean_apply_4(v_recur_396_, v_it_397_, v_a_401_, lean_box(0), lean_box(0));
        return v___x_402_;
    }
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(
    mut v_toPure_403_: *mut LeanObject,
    mut v_recur_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
    mut v_acc_406_: *mut LeanObject,
    mut v_toBind_407_: *mut LeanObject,
    mut v_s_408_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_408_) {
        0 => {
            let mut v_it_409_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_410_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_411_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
            v_it_409_ = lean_ctor_get(v_s_408_, 0);
            lean_inc(v_it_409_);
            v_out_410_ = lean_ctor_get(v_s_408_, 1);
            lean_inc(v_out_410_);
            lean_dec_ref_known(v_s_408_, 2);
            v___f_411_ = lean_alloc_closure(
                l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_411_, 0, v_toPure_403_);
            lean_closure_set(v___f_411_, 1, v_recur_404_);
            lean_closure_set(v___f_411_, 2, v_it_409_);
            v___x_412_ = lean_apply_3(v___y_405_, v_out_410_, lean_box(0), v_acc_406_);
            v___x_413_ = lean_apply_4(
                v_toBind_407_,
                lean_box(0),
                lean_box(0),
                v___x_412_,
                v___f_411_,
            );
            return v___x_413_;
        }
        1 => {
            let mut v_it_414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_407_);
            lean_dec(v___y_405_);
            lean_dec(v_toPure_403_);
            v_it_414_ = lean_ctor_get(v_s_408_, 0);
            lean_inc(v_it_414_);
            lean_dec_ref_known(v_s_408_, 1);
            v___x_415_ = lean_apply_4(
                v_recur_404_,
                v_it_414_,
                v_acc_406_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_415_;
        }
        _ => {
            let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_407_);
            lean_dec(v___y_405_);
            lean_dec(v_recur_404_);
            v___x_416_ = lean_apply_2(v_toPure_403_, lean_box(0), v_acc_406_);
            return v___x_416_;
        }
    }
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(
    mut v_toPure_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v_toBind_419_: *mut LeanObject,
    mut v_lift_420_: *mut LeanObject,
    mut v_it_421_: *mut LeanObject,
    mut v_acc_422_: *mut LeanObject,
    mut v_hP_423_: *mut LeanObject,
    mut v_recur_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___f_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_425_ = lean_ctor_get(v_it_421_, 0);
                v_start_426_ = lean_ctor_get(v_it_421_, 1);
                v_stop_427_ = lean_ctor_get(v_it_421_, 2);
                v_isSharedCheck_443_ = (!lean_is_exclusive(v_it_421_)) as u8;
                if v_isSharedCheck_443_ == 0 {
                    v___x_429_ = v_it_421_;
                    v_isShared_430_ = v_isSharedCheck_443_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_427_);
                    lean_inc(v_start_426_);
                    lean_inc(v_array_425_);
                    lean_dec(v_it_421_);
                    v___x_429_ = lean_box(0);
                    v_isShared_430_ = v_isSharedCheck_443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_431_ = lean_alloc_closure(
                    l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___f_431_, 0, v_toPure_417_);
                lean_closure_set(v___f_431_, 1, v_recur_424_);
                lean_closure_set(v___f_431_, 2, v___y_418_);
                lean_closure_set(v___f_431_, 3, v_acc_422_);
                lean_closure_set(v___f_431_, 4, v_toBind_419_);
                v___x_432_ = lean_nat_dec_lt(v_start_426_, v_stop_427_);
                if v___x_432_ == 0 {
                    lean_del_object(v___x_429_);
                    lean_dec(v_stop_427_);
                    lean_dec(v_start_426_);
                    lean_dec_ref(v_array_425_);
                    v___x_433_ = lean_box(2);
                    v___x_434_ = lean_apply_4(
                        v_lift_420_,
                        lean_box(0),
                        lean_box(0),
                        v___f_431_,
                        v___x_433_,
                    );
                    return v___x_434_;
                } else {
                    v___x_435_ = lean_unsigned_to_nat(1);
                    v___x_436_ = lean_nat_add(v_start_426_, v___x_435_);
                    lean_inc_ref(v_array_425_);
                    if v_isShared_430_ == 0 {
                        lean_ctor_set(v___x_429_, 1, v___x_436_);
                        v___x_438_ = v___x_429_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_442_, 0, v_array_425_);
                        lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_436_);
                        lean_ctor_set(v_reuseFailAlloc_442_, 2, v_stop_427_);
                        v___x_438_ = v_reuseFailAlloc_442_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_439_ = lean_array_fget(v_array_425_, v_start_426_);
                lean_dec(v_start_426_);
                lean_dec_ref(v_array_425_);
                v___x_440_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_440_, 0, v___x_438_);
                lean_ctor_set(v___x_440_, 1, v___x_439_);
                v___x_441_ = lean_apply_4(
                    v_lift_420_,
                    lean_box(0),
                    lean_box(0),
                    v___f_431_,
                    v___x_440_,
                );
                return v___x_441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3(
    mut v_inst_444_: *mut LeanObject,
    mut v_lift_445_: *mut LeanObject,
    mut v_00_u03b3_446_: *mut LeanObject,
    mut v_Pl_447_: *mut LeanObject,
    mut v_it_448_: *mut LeanObject,
    mut v_init_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_451_ = lean_ctor_get(v_inst_444_, 0);
    lean_inc_ref(v_toApplicative_451_);
    v_toBind_452_ = lean_ctor_get(v_inst_444_, 1);
    lean_inc(v_toBind_452_);
    lean_dec_ref(v_inst_444_);
    v_toPure_453_ = lean_ctor_get(v_toApplicative_451_, 1);
    lean_inc(v_toPure_453_);
    lean_dec_ref(v_toApplicative_451_);
    v___f_454_ = lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_454_, 0, v_toPure_453_);
    lean_closure_set(v___f_454_, 1, v___y_450_);
    lean_closure_set(v___f_454_, 2, v_toBind_452_);
    lean_closure_set(v___f_454_, 3, v_lift_445_);
    v___x_455_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_454_, v_it_448_, v_init_449_, lean_box(0));
    return v___x_455_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(
    mut v_inst_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_457_: *mut LeanObject = core::ptr::null_mut();
    v___f_457_ = lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_457_, 0, v_inst_456_);
    return v___f_457_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad(
    mut v_00_u03b1_458_: *mut LeanObject,
    mut v_m_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_461_: *mut LeanObject = core::ptr::null_mut();
    v___f_461_ = lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_461_, 0, v_inst_460_);
    return v___f_461_;
}
pub unsafe fn l_Subarray_instToIterator___lam__0(mut v_x_462_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_x_462_);
    return v_x_462_;
}
pub unsafe fn l_Subarray_instToIterator___lam__0___boxed(
    mut v_x_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_464_: *mut LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Subarray_instToIterator___lam__0(v_x_463_);
    lean_dec_ref(v_x_463_);
    return v_res_464_;
}
pub unsafe fn l_Subarray_instToIterator(mut v_00_u03b1_466_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_467_: *mut LeanObject = core::ptr::null_mut();
    v___f_467_ = l_Subarray_instToIterator___closed__0;
    return v___f_467_;
}
pub unsafe fn l_instForInSubarrayOfMonad___redArg(
    mut v_inst_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___f_469_ = l_Subarray_instToIterator___closed__0;
    lean_inc_ref(v_inst_468_);
    v___f_470_ = lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_470_, 0, v_inst_468_);
    v___x_471_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
        v_inst_468_,
        v___f_469_,
        v___f_470_,
    );
    return v___x_471_;
}
pub unsafe fn l_instForInSubarrayOfMonad(
    mut v_00_u03b1_472_: *mut LeanObject,
    mut v_m_473_: *mut LeanObject,
    mut v_inst_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = l_instForInSubarrayOfMonad___redArg(v_inst_474_);
    return v___x_475_;
}
pub unsafe fn l_Subarray_forIn___redArg___lam__0(
    mut v_toPure_476_: *mut LeanObject,
    mut v_____do__lift_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = lean_apply_2(v_toPure_476_, lean_box(0), v_____do__lift_477_);
    return v___x_478_;
}
pub unsafe fn l_Subarray_forIn___redArg___lam__1(
    mut v_toPure_479_: *mut LeanObject,
    mut v_recur_480_: *mut LeanObject,
    mut v___x_481_: *mut LeanObject,
    mut v_____do__lift_482_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_482_) == 0 {
        let mut v_a_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_481_);
        lean_dec(v_recur_480_);
        v_a_483_ = lean_ctor_get(v_____do__lift_482_, 0);
        lean_inc(v_a_483_);
        lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_484_ = lean_apply_2(v_toPure_479_, lean_box(0), v_a_483_);
        return v___x_484_;
    } else {
        let mut v_a_485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_479_);
        v_a_485_ = lean_ctor_get(v_____do__lift_482_, 0);
        lean_inc(v_a_485_);
        lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_486_ = lean_apply_4(v_recur_480_, v___x_481_, v_a_485_, lean_box(0), lean_box(0));
        return v___x_486_;
    }
}
pub unsafe fn l_Subarray_forIn___redArg___lam__2(
    mut v_toPure_487_: *mut LeanObject,
    mut v_f_488_: *mut LeanObject,
    mut v_toBind_489_: *mut LeanObject,
    mut v___f_490_: *mut LeanObject,
    mut v_it_491_: *mut LeanObject,
    mut v_acc_492_: *mut LeanObject,
    mut v_hP_493_: *mut LeanObject,
    mut v_recur_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_495_ = lean_ctor_get(v_it_491_, 0);
                v_start_496_ = lean_ctor_get(v_it_491_, 1);
                v_stop_497_ = lean_ctor_get(v_it_491_, 2);
                v_isSharedCheck_513_ = (!lean_is_exclusive(v_it_491_)) as u8;
                if v_isSharedCheck_513_ == 0 {
                    v___x_499_ = v_it_491_;
                    v_isShared_500_ = v_isSharedCheck_513_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_497_);
                    lean_inc(v_start_496_);
                    lean_inc(v_array_495_);
                    lean_dec(v_it_491_);
                    v___x_499_ = lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_501_ = lean_nat_dec_lt(v_start_496_, v_stop_497_);
                if v___x_501_ == 0 {
                    lean_del_object(v___x_499_);
                    lean_dec(v_stop_497_);
                    lean_dec(v_start_496_);
                    lean_dec_ref(v_array_495_);
                    lean_dec(v_recur_494_);
                    lean_dec(v___f_490_);
                    lean_dec(v_toBind_489_);
                    lean_dec(v_f_488_);
                    v___x_502_ = lean_apply_2(v_toPure_487_, lean_box(0), v_acc_492_);
                    return v___x_502_;
                } else {
                    v___x_503_ = lean_unsigned_to_nat(1);
                    v___x_504_ = lean_nat_add(v_start_496_, v___x_503_);
                    lean_inc_ref(v_array_495_);
                    if v_isShared_500_ == 0 {
                        lean_ctor_set(v___x_499_, 1, v___x_504_);
                        v___x_506_ = v___x_499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_512_, 0, v_array_495_);
                        lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_504_);
                        lean_ctor_set(v_reuseFailAlloc_512_, 2, v_stop_497_);
                        v___x_506_ = v_reuseFailAlloc_512_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___f_507_ = lean_alloc_closure(
                    l_Subarray_forIn___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_507_, 0, v_toPure_487_);
                lean_closure_set(v___f_507_, 1, v_recur_494_);
                lean_closure_set(v___f_507_, 2, v___x_506_);
                v___x_508_ = lean_array_fget(v_array_495_, v_start_496_);
                lean_dec(v_start_496_);
                lean_dec_ref(v_array_495_);
                v___x_509_ = lean_apply_2(v_f_488_, v___x_508_, v_acc_492_);
                lean_inc(v_toBind_489_);
                v___x_510_ = lean_apply_4(
                    v_toBind_489_,
                    lean_box(0),
                    lean_box(0),
                    v___x_509_,
                    v___f_490_,
                );
                v___x_511_ = lean_apply_4(
                    v_toBind_489_,
                    lean_box(0),
                    lean_box(0),
                    v___x_510_,
                    v___f_507_,
                );
                return v___x_511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_forIn___redArg(
    mut v_inst_514_: *mut LeanObject,
    mut v_s_515_: *mut LeanObject,
    mut v_b_516_: *mut LeanObject,
    mut v_f_517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_518_ = lean_ctor_get(v_inst_514_, 0);
    lean_inc_ref(v_toApplicative_518_);
    v_toBind_519_ = lean_ctor_get(v_inst_514_, 1);
    lean_inc(v_toBind_519_);
    lean_dec_ref(v_inst_514_);
    v_toPure_520_ = lean_ctor_get(v_toApplicative_518_, 1);
    lean_inc_n(v_toPure_520_, 2);
    lean_dec_ref(v_toApplicative_518_);
    v___f_521_ = lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_521_, 0, v_toPure_520_);
    v___f_522_ = lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_522_, 0, v_toPure_520_);
    lean_closure_set(v___f_522_, 1, v_f_517_);
    lean_closure_set(v___f_522_, 2, v_toBind_519_);
    lean_closure_set(v___f_522_, 3, v___f_521_);
    v___x_523_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_522_, v_s_515_, v_b_516_, lean_box(0));
    return v___x_523_;
}
pub unsafe fn l_Subarray_forIn(
    mut v_00_u03b1_524_: *mut LeanObject,
    mut v_00_u03b2_525_: *mut LeanObject,
    mut v_m_526_: *mut LeanObject,
    mut v_inst_527_: *mut LeanObject,
    mut v_s_528_: *mut LeanObject,
    mut v_b_529_: *mut LeanObject,
    mut v_f_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_531_ = lean_ctor_get(v_inst_527_, 0);
    lean_inc_ref(v_toApplicative_531_);
    v_toBind_532_ = lean_ctor_get(v_inst_527_, 1);
    lean_inc(v_toBind_532_);
    lean_dec_ref(v_inst_527_);
    v_toPure_533_ = lean_ctor_get(v_toApplicative_531_, 1);
    lean_inc_n(v_toPure_533_, 2);
    lean_dec_ref(v_toApplicative_531_);
    v___f_534_ = lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_534_, 0, v_toPure_533_);
    v___f_535_ = lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_535_, 0, v_toPure_533_);
    lean_closure_set(v___f_535_, 1, v_f_530_);
    lean_closure_set(v___f_535_, 2, v_toBind_532_);
    lean_closure_set(v___f_535_, 3, v___f_534_);
    v___x_536_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_535_, v_s_528_, v_b_529_, lean_box(0));
    return v___x_536_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(
    mut v_a_537_: *mut LeanObject,
    mut v_b_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_539_ = lean_ctor_get(v_a_537_, 0);
                v_start_540_ = lean_ctor_get(v_a_537_, 1);
                v_stop_541_ = lean_ctor_get(v_a_537_, 2);
                v_isSharedCheck_554_ = (!lean_is_exclusive(v_a_537_)) as u8;
                if v_isSharedCheck_554_ == 0 {
                    v___x_543_ = v_a_537_;
                    v_isShared_544_ = v_isSharedCheck_554_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_541_);
                    lean_inc(v_start_540_);
                    lean_inc(v_array_539_);
                    lean_dec(v_a_537_);
                    v___x_543_ = lean_box(0);
                    v_isShared_544_ = v_isSharedCheck_554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_545_ = lean_nat_dec_lt(v_start_540_, v_stop_541_);
                if v___x_545_ == 0 {
                    lean_del_object(v___x_543_);
                    lean_dec(v_stop_541_);
                    lean_dec(v_start_540_);
                    lean_dec_ref(v_array_539_);
                    return v_b_538_;
                } else {
                    v___x_546_ = lean_unsigned_to_nat(1);
                    v___x_547_ = lean_nat_add(v_start_540_, v___x_546_);
                    lean_inc_ref(v_array_539_);
                    if v_isShared_544_ == 0 {
                        lean_ctor_set(v___x_543_, 1, v___x_547_);
                        v___x_549_ = v___x_543_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_553_, 0, v_array_539_);
                        lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_547_);
                        lean_ctor_set(v_reuseFailAlloc_553_, 2, v_stop_541_);
                        v___x_549_ = v_reuseFailAlloc_553_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_550_ = lean_array_fget(v_array_539_, v_start_540_);
                lean_dec(v_start_540_);
                lean_dec_ref(v_array_539_);
                v___x_551_ = lean_array_push(v_b_538_, v___x_550_);
                v_a_537_ = v___x_549_;
                v_b_538_ = v___x_551_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_copy___redArg(mut v_s_557_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Subarray_copy___redArg___closed__0;
    v___x_559_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_557_, v___x_558_);
    return v___x_559_;
}
pub unsafe fn l_Subarray_copy(
    mut v_00_u03b1_560_: *mut LeanObject,
    mut v_s_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Subarray_copy___redArg(v_s_561_);
    return v___x_562_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(
    mut v_00_u03b1_563_: *mut LeanObject,
    mut v_inst_564_: *mut LeanObject,
    mut v_R_565_: *mut LeanObject,
    mut v_a_566_: *mut LeanObject,
    mut v_b_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    v___x_568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_566_, v_b_567_);
    return v___x_568_;
}
pub unsafe fn l_instCoeSubarrayArray(mut v_00_u03b1_570_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = l_instCoeSubarrayArray___closed__0;
    return v___x_571_;
}
pub unsafe fn l_Array_ofSubarray___redArg(mut v_s_572_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Subarray_copy___redArg___closed__0;
    v___x_574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_572_, v___x_573_);
    return v___x_574_;
}
pub unsafe fn l_Array_ofSubarray(
    mut v_00_u03b1_575_: *mut LeanObject,
    mut v_s_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ = l_Array_ofSubarray___redArg(v_s_576_);
    return v___x_577_;
}
pub unsafe fn l_Array_instAppendSubarray___lam__0(
    mut v_it_578_: *mut LeanObject,
    mut v_acc_579_: *mut LeanObject,
    mut v_recur_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_581_ = lean_ctor_get(v_it_578_, 0);
                v_start_582_ = lean_ctor_get(v_it_578_, 1);
                v_stop_583_ = lean_ctor_get(v_it_578_, 2);
                v_isSharedCheck_596_ = (!lean_is_exclusive(v_it_578_)) as u8;
                if v_isSharedCheck_596_ == 0 {
                    v___x_585_ = v_it_578_;
                    v_isShared_586_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_583_);
                    lean_inc(v_start_582_);
                    lean_inc(v_array_581_);
                    lean_dec(v_it_578_);
                    v___x_585_ = lean_box(0);
                    v_isShared_586_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_587_ = lean_nat_dec_lt(v_start_582_, v_stop_583_);
                if v___x_587_ == 0 {
                    lean_del_object(v___x_585_);
                    lean_dec(v_stop_583_);
                    lean_dec(v_start_582_);
                    lean_dec_ref(v_array_581_);
                    lean_dec_ref(v_recur_580_);
                    return v_acc_579_;
                } else {
                    v___x_588_ = lean_unsigned_to_nat(1);
                    v___x_589_ = lean_nat_add(v_start_582_, v___x_588_);
                    lean_inc_ref(v_array_581_);
                    if v_isShared_586_ == 0 {
                        lean_ctor_set(v___x_585_, 1, v___x_589_);
                        v___x_591_ = v___x_585_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_595_, 0, v_array_581_);
                        lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_589_);
                        lean_ctor_set(v_reuseFailAlloc_595_, 2, v_stop_583_);
                        v___x_591_ = v_reuseFailAlloc_595_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_592_ = lean_array_fget(v_array_581_, v_start_582_);
                lean_dec(v_start_582_);
                lean_dec_ref(v_array_581_);
                v___x_593_ = lean_array_push(v_acc_579_, v___x_592_);
                v___x_594_ = lean_apply_3(v_recur_580_, v___x_591_, v___x_593_, lean_box(0));
                return v___x_594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_instAppendSubarray___lam__2(
    mut v___f_597_: *mut LeanObject,
    mut v___f_598_: *mut LeanObject,
    mut v_x_599_: *mut LeanObject,
    mut v_y_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = lean_unsigned_to_nat(0);
    v___x_602_ = l_Subarray_copy___redArg___closed__0;
    v___x_603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_597_, v_x_599_, v___x_602_,
    );
    v___x_604_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_598_, v_y_600_, v___x_602_,
    );
    v_a_605_ = l_Array_append___redArg(v___x_603_, v___x_604_);
    lean_dec(v___x_604_);
    v___x_606_ = lean_array_get_size(v_a_605_);
    v___x_607_ = l_Array_toSubarray___redArg(v_a_605_, v___x_601_, v___x_606_);
    return v___x_607_;
}
pub unsafe fn l_Array_instAppendSubarray(mut v_00_u03b1_611_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_612_: *mut LeanObject = core::ptr::null_mut();
    v___f_612_ = l_Array_instAppendSubarray___closed__1;
    return v___f_612_;
}
pub unsafe fn l_Array_Subarray_repr___redArg(
    mut v_inst_616_: *mut LeanObject,
    mut v_s_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    v___f_618_ = l_Array_instAppendSubarray___closed__0;
    v___x_619_ = l_Subarray_copy___redArg___closed__0;
    v___x_620_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_618_, v_s_617_, v___x_619_,
    );
    v___x_621_ = l_Array_repr___redArg(v_inst_616_, v___x_620_);
    v___x_622_ = l_Array_Subarray_repr___redArg___closed__1;
    v___x_623_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_623_, 0, v___x_621_);
    lean_ctor_set(v___x_623_, 1, v___x_622_);
    return v___x_623_;
}
pub unsafe fn l_Array_Subarray_repr(
    mut v_00_u03b1_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
    mut v_s_626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    v___x_627_ = l_Array_Subarray_repr___redArg(v_inst_625_, v_s_626_);
    return v___x_627_;
}
pub unsafe fn l_Array_instReprSubarray___redArg___lam__0(
    mut v_inst_628_: *mut LeanObject,
    mut v_s_629_: *mut LeanObject,
    mut v_x_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Array_Subarray_repr___redArg(v_inst_628_, v_s_629_);
    return v___x_631_;
}
pub unsafe fn l_Array_instReprSubarray___redArg___lam__0___boxed(
    mut v_inst_632_: *mut LeanObject,
    mut v_s_633_: *mut LeanObject,
    mut v_x_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_635_: *mut LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_632_, v_s_633_, v_x_634_);
    lean_dec(v_x_634_);
    return v_res_635_;
}
pub unsafe fn l_Array_instReprSubarray___redArg(
    mut v_inst_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_637_: *mut LeanObject = core::ptr::null_mut();
    v___f_637_ = lean_alloc_closure(
        l_Array_instReprSubarray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_637_, 0, v_inst_636_);
    return v___f_637_;
}
pub unsafe fn l_Array_instReprSubarray(
    mut v_00_u03b1_638_: *mut LeanObject,
    mut v_inst_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_640_: *mut LeanObject = core::ptr::null_mut();
    v___f_640_ = lean_alloc_closure(
        l_Array_instReprSubarray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_640_, 0, v_inst_639_);
    return v___f_640_;
}
pub unsafe fn l_Array_instToStringSubarray___redArg___lam__1(
    mut v___f_642_: *mut LeanObject,
    mut v_inst_643_: *mut LeanObject,
    mut v_s_644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Subarray_copy___redArg___closed__0;
    v___x_646_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_642_, v_s_644_, v___x_645_,
    );
    v___x_647_ = l_Array_instToStringSubarray___redArg___lam__1___closed__0;
    v___x_648_ = lean_array_to_list(v___x_646_);
    v___x_649_ = l_List_toString___redArg(v_inst_643_, v___x_648_);
    v___x_650_ = lean_string_append(v___x_647_, v___x_649_);
    lean_dec_ref(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_Array_instToStringSubarray___redArg(
    mut v_inst_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut LeanObject = core::ptr::null_mut();
    v___f_652_ = l_Array_instAppendSubarray___closed__0;
    v___f_653_ = lean_alloc_closure(
        l_Array_instToStringSubarray___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_653_, 0, v___f_652_);
    lean_closure_set(v___f_653_, 1, v_inst_651_);
    return v___f_653_;
}
pub unsafe fn l_Array_instToStringSubarray(
    mut v_00_u03b1_654_: *mut LeanObject,
    mut v_inst_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    v___x_656_ = l_Array_instToStringSubarray___redArg(v_inst_655_);
    return v___x_656_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Array_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Slice_Array_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_Array_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Operations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Slice_Array_Iterator(builtin);
}
