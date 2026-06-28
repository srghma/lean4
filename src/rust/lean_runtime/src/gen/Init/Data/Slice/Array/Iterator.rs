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
pub static l_instIteratorSubarrayIteratorId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instIteratorSubarrayIteratorId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instIteratorSubarrayIteratorId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instIteratorSubarrayIteratorId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_instToIterator___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Subarray_instToIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Subarray_instToIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_instToIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Subarray_copy___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Subarray_copy___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Subarray_copy___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instCoeSubarrayArray___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Subarray_copy as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instCoeSubarrayArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instCoeSubarrayArray___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_instAppendSubarray___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Array_instAppendSubarray___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_instAppendSubarray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instAppendSubarray___closed__1_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instAppendSubarray___lam__2 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_instAppendSubarray___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_instAppendSubarray___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instAppendSubarray___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_Subarray_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Array_Subarray_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_Subarray_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_Subarray_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_Subarray_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_instToStringSubarray___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Array_instToStringSubarray___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_instToStringSubarray___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_SubarrayIterator_step___redArg(
    mut v_x_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_335_: u8 = 0;
    let mut v___x_336_: u8 = 0;
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_330_ = crate::leanh::lean_ctor_get(v_x_329_, 0);
                v_start_331_ = crate::leanh::lean_ctor_get(v_x_329_, 1);
                v_stop_332_ = crate::leanh::lean_ctor_get(v_x_329_, 2);
                v_isSharedCheck_345_ = (!crate::leanh::lean_is_exclusive(v_x_329_)) as u8;
                if v_isSharedCheck_345_ == 0 {
                    v___x_334_ = v_x_329_;
                    v_isShared_335_ = v_isSharedCheck_345_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_332_);
                    crate::leanh::lean_inc(v_start_331_);
                    crate::leanh::lean_inc(v_array_330_);
                    crate::leanh::lean_dec(v_x_329_);
                    v___x_334_ = crate::leanh::lean_box(0);
                    v_isShared_335_ = v_isSharedCheck_345_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_336_ = lean_nat_dec_lt(v_start_331_, v_stop_332_);
                if v___x_336_ == 0 {
                    crate::leanh::lean_del_object(v___x_334_);
                    crate::leanh::lean_dec(v_stop_332_);
                    crate::leanh::lean_dec(v_start_331_);
                    crate::leanh::lean_dec_ref(v_array_330_);
                    v___x_337_ = crate::leanh::lean_box(2);
                    return v___x_337_;
                } else {
                    v___x_338_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_339_ = lean_nat_add(v_start_331_, v___x_338_);
                    crate::leanh::lean_inc_ref(v_array_330_);
                    if v_isShared_335_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_334_, 1, v___x_339_);
                        v___x_341_ = v___x_334_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_344_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_344_, 0, v_array_330_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_344_, 1, v___x_339_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_344_, 2, v_stop_332_);
                        v___x_341_ = v_reuseFailAlloc_344_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_342_ = lean_array_fget(v_array_330_, v_start_331_);
                crate::leanh::lean_dec(v_start_331_);
                crate::leanh::lean_dec_ref(v_array_330_);
                v___x_343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_343_, 0, v___x_341_);
                crate::leanh::lean_ctor_set(v___x_343_, 1, v___x_342_);
                return v___x_343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_SubarrayIterator_step(
    mut v_00_u03b1_346_: *mut crate::leanh::LeanObject,
    mut v_m_347_: *mut crate::leanh::LeanObject,
    mut v_x_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_354_: u8 = 0;
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_349_ = crate::leanh::lean_ctor_get(v_x_348_, 0);
                v_start_350_ = crate::leanh::lean_ctor_get(v_x_348_, 1);
                v_stop_351_ = crate::leanh::lean_ctor_get(v_x_348_, 2);
                v_isSharedCheck_364_ = (!crate::leanh::lean_is_exclusive(v_x_348_)) as u8;
                if v_isSharedCheck_364_ == 0 {
                    v___x_353_ = v_x_348_;
                    v_isShared_354_ = v_isSharedCheck_364_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_351_);
                    crate::leanh::lean_inc(v_start_350_);
                    crate::leanh::lean_inc(v_array_349_);
                    crate::leanh::lean_dec(v_x_348_);
                    v___x_353_ = crate::leanh::lean_box(0);
                    v_isShared_354_ = v_isSharedCheck_364_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_355_ = lean_nat_dec_lt(v_start_350_, v_stop_351_);
                if v___x_355_ == 0 {
                    crate::leanh::lean_del_object(v___x_353_);
                    crate::leanh::lean_dec(v_stop_351_);
                    crate::leanh::lean_dec(v_start_350_);
                    crate::leanh::lean_dec_ref(v_array_349_);
                    v___x_356_ = crate::leanh::lean_box(2);
                    return v___x_356_;
                } else {
                    v___x_357_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_358_ = lean_nat_add(v_start_350_, v___x_357_);
                    crate::leanh::lean_inc_ref(v_array_349_);
                    if v_isShared_354_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_353_, 1, v___x_358_);
                        v___x_360_ = v___x_353_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_363_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_363_, 0, v_array_349_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_358_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_363_, 2, v_stop_351_);
                        v___x_360_ = v_reuseFailAlloc_363_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_361_ = lean_array_fget(v_array_349_, v_start_350_);
                crate::leanh::lean_dec(v_start_350_);
                crate::leanh::lean_dec_ref(v_array_349_);
                v___x_362_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_362_, 0, v___x_360_);
                crate::leanh::lean_ctor_set(v___x_362_, 1, v___x_361_);
                return v___x_362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instIteratorSubarrayIteratorId___lam__0(
    mut v_it_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_371_: u8 = 0;
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_366_ = crate::leanh::lean_ctor_get(v_it_365_, 0);
                v_start_367_ = crate::leanh::lean_ctor_get(v_it_365_, 1);
                v_stop_368_ = crate::leanh::lean_ctor_get(v_it_365_, 2);
                v_isSharedCheck_381_ = (!crate::leanh::lean_is_exclusive(v_it_365_)) as u8;
                if v_isSharedCheck_381_ == 0 {
                    v___x_370_ = v_it_365_;
                    v_isShared_371_ = v_isSharedCheck_381_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_368_);
                    crate::leanh::lean_inc(v_start_367_);
                    crate::leanh::lean_inc(v_array_366_);
                    crate::leanh::lean_dec(v_it_365_);
                    v___x_370_ = crate::leanh::lean_box(0);
                    v_isShared_371_ = v_isSharedCheck_381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_372_ = lean_nat_dec_lt(v_start_367_, v_stop_368_);
                if v___x_372_ == 0 {
                    crate::leanh::lean_del_object(v___x_370_);
                    crate::leanh::lean_dec(v_stop_368_);
                    crate::leanh::lean_dec(v_start_367_);
                    crate::leanh::lean_dec_ref(v_array_366_);
                    v___x_373_ = crate::leanh::lean_box(2);
                    return v___x_373_;
                } else {
                    v___x_374_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_375_ = lean_nat_add(v_start_367_, v___x_374_);
                    crate::leanh::lean_inc_ref(v_array_366_);
                    if v_isShared_371_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_370_, 1, v___x_375_);
                        v___x_377_ = v___x_370_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_380_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_380_, 0, v_array_366_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_375_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_380_, 2, v_stop_368_);
                        v___x_377_ = v_reuseFailAlloc_380_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_378_ = lean_array_fget(v_array_366_, v_start_367_);
                crate::leanh::lean_dec(v_start_367_);
                crate::leanh::lean_dec_ref(v_array_366_);
                v___x_379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_379_, 0, v___x_377_);
                crate::leanh::lean_ctor_set(v___x_379_, 1, v___x_378_);
                return v___x_379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instIteratorSubarrayIteratorId(
    mut v_00_u03b1_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_384_ = l_instIteratorSubarrayIteratorId___closed__0;
    return v___f_384_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter___redArg(
    mut v_x_385_: *mut crate::leanh::LeanObject,
    mut v_h__1_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = crate::leanh::lean_apply_1(v_h__1_386_, v_x_385_);
    return v___x_387_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_step_match__1_splitter(
    mut v_00_u03b1_388_: *mut crate::leanh::LeanObject,
    mut v_motive_389_: *mut crate::leanh::LeanObject,
    mut v_x_390_: *mut crate::leanh::LeanObject,
    mut v_h__1_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_392_ = crate::leanh::lean_apply_1(v_h__1_391_, v_x_390_);
    return v___x_392_;
}
pub unsafe fn l___private_Init_Data_Slice_Array_Iterator_0__SubarrayIterator_instFinitelessRelation(
    mut v_00_u03b1_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_394_ = crate::leanh::lean_box(0);
    return v___x_394_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0(
    mut v_toPure_395_: *mut crate::leanh::LeanObject,
    mut v_recur_396_: *mut crate::leanh::LeanObject,
    mut v_it_397_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_398_) == 0 {
        let mut v_a_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_397_);
        crate::leanh::lean_dec(v_recur_396_);
        v_a_399_ = crate::leanh::lean_ctor_get(v_____do__lift_398_, 0);
        crate::leanh::lean_inc(v_a_399_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_398_, 1);
        v___x_400_ = crate::leanh::lean_apply_2(v_toPure_395_, crate::leanh::lean_box(0), v_a_399_);
        return v___x_400_;
    } else {
        let mut v_a_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_395_);
        v_a_401_ = crate::leanh::lean_ctor_get(v_____do__lift_398_, 0);
        crate::leanh::lean_inc(v_a_401_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_398_, 1);
        v___x_402_ = crate::leanh::lean_apply_4(
            v_recur_396_,
            v_it_397_,
            v_a_401_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_402_;
    }
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1(
    mut v_toPure_403_: *mut crate::leanh::LeanObject,
    mut v_recur_404_: *mut crate::leanh::LeanObject,
    mut v___y_405_: *mut crate::leanh::LeanObject,
    mut v_acc_406_: *mut crate::leanh::LeanObject,
    mut v_toBind_407_: *mut crate::leanh::LeanObject,
    mut v_s_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_408_) {
        0 => {
            let mut v_it_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_409_ = crate::leanh::lean_ctor_get(v_s_408_, 0);
            crate::leanh::lean_inc(v_it_409_);
            v_out_410_ = crate::leanh::lean_ctor_get(v_s_408_, 1);
            crate::leanh::lean_inc(v_out_410_);
            crate::leanh::lean_dec_ref_known(v_s_408_, 2);
            v___f_411_ = crate::leanh::lean_alloc_closure(
                l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_411_, 0, v_toPure_403_);
            crate::leanh::lean_closure_set(v___f_411_, 1, v_recur_404_);
            crate::leanh::lean_closure_set(v___f_411_, 2, v_it_409_);
            v___x_412_ = crate::leanh::lean_apply_3(
                v___y_405_,
                v_out_410_,
                crate::leanh::lean_box(0),
                v_acc_406_,
            );
            v___x_413_ = crate::leanh::lean_apply_4(
                v_toBind_407_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_412_,
                v___f_411_,
            );
            return v___x_413_;
        }
        1 => {
            let mut v_it_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_407_);
            crate::leanh::lean_dec(v___y_405_);
            crate::leanh::lean_dec(v_toPure_403_);
            v_it_414_ = crate::leanh::lean_ctor_get(v_s_408_, 0);
            crate::leanh::lean_inc(v_it_414_);
            crate::leanh::lean_dec_ref_known(v_s_408_, 1);
            v___x_415_ = crate::leanh::lean_apply_4(
                v_recur_404_,
                v_it_414_,
                v_acc_406_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_415_;
        }
        _ => {
            let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_407_);
            crate::leanh::lean_dec(v___y_405_);
            crate::leanh::lean_dec(v_recur_404_);
            v___x_416_ =
                crate::leanh::lean_apply_2(v_toPure_403_, crate::leanh::lean_box(0), v_acc_406_);
            return v___x_416_;
        }
    }
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2(
    mut v_toPure_417_: *mut crate::leanh::LeanObject,
    mut v___y_418_: *mut crate::leanh::LeanObject,
    mut v_toBind_419_: *mut crate::leanh::LeanObject,
    mut v_lift_420_: *mut crate::leanh::LeanObject,
    mut v_it_421_: *mut crate::leanh::LeanObject,
    mut v_acc_422_: *mut crate::leanh::LeanObject,
    mut v_hP_423_: *mut crate::leanh::LeanObject,
    mut v_recur_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___f_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_425_ = crate::leanh::lean_ctor_get(v_it_421_, 0);
                v_start_426_ = crate::leanh::lean_ctor_get(v_it_421_, 1);
                v_stop_427_ = crate::leanh::lean_ctor_get(v_it_421_, 2);
                v_isSharedCheck_443_ = (!crate::leanh::lean_is_exclusive(v_it_421_)) as u8;
                if v_isSharedCheck_443_ == 0 {
                    v___x_429_ = v_it_421_;
                    v_isShared_430_ = v_isSharedCheck_443_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_427_);
                    crate::leanh::lean_inc(v_start_426_);
                    crate::leanh::lean_inc(v_array_425_);
                    crate::leanh::lean_dec(v_it_421_);
                    v___x_429_ = crate::leanh::lean_box(0);
                    v_isShared_430_ = v_isSharedCheck_443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_431_ = crate::leanh::lean_alloc_closure(
                    l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_431_, 0, v_toPure_417_);
                crate::leanh::lean_closure_set(v___f_431_, 1, v_recur_424_);
                crate::leanh::lean_closure_set(v___f_431_, 2, v___y_418_);
                crate::leanh::lean_closure_set(v___f_431_, 3, v_acc_422_);
                crate::leanh::lean_closure_set(v___f_431_, 4, v_toBind_419_);
                v___x_432_ = lean_nat_dec_lt(v_start_426_, v_stop_427_);
                if v___x_432_ == 0 {
                    crate::leanh::lean_del_object(v___x_429_);
                    crate::leanh::lean_dec(v_stop_427_);
                    crate::leanh::lean_dec(v_start_426_);
                    crate::leanh::lean_dec_ref(v_array_425_);
                    v___x_433_ = crate::leanh::lean_box(2);
                    v___x_434_ = crate::leanh::lean_apply_4(
                        v_lift_420_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_431_,
                        v___x_433_,
                    );
                    return v___x_434_;
                } else {
                    v___x_435_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_436_ = lean_nat_add(v_start_426_, v___x_435_);
                    crate::leanh::lean_inc_ref(v_array_425_);
                    if v_isShared_430_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_429_, 1, v___x_436_);
                        v___x_438_ = v___x_429_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_442_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 0, v_array_425_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_436_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 2, v_stop_427_);
                        v___x_438_ = v_reuseFailAlloc_442_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_439_ = lean_array_fget(v_array_425_, v_start_426_);
                crate::leanh::lean_dec(v_start_426_);
                crate::leanh::lean_dec_ref(v_array_425_);
                v___x_440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_440_, 0, v___x_438_);
                crate::leanh::lean_ctor_set(v___x_440_, 1, v___x_439_);
                v___x_441_ = crate::leanh::lean_apply_4(
                    v_lift_420_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_444_: *mut crate::leanh::LeanObject,
    mut v_lift_445_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_446_: *mut crate::leanh::LeanObject,
    mut v_Pl_447_: *mut crate::leanh::LeanObject,
    mut v_it_448_: *mut crate::leanh::LeanObject,
    mut v_init_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_451_ = crate::leanh::lean_ctor_get(v_inst_444_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_451_);
    v_toBind_452_ = crate::leanh::lean_ctor_get(v_inst_444_, 1);
    crate::leanh::lean_inc(v_toBind_452_);
    crate::leanh::lean_dec_ref(v_inst_444_);
    v_toPure_453_ = crate::leanh::lean_ctor_get(v_toApplicative_451_, 1);
    crate::leanh::lean_inc(v_toPure_453_);
    crate::leanh::lean_dec_ref(v_toApplicative_451_);
    v___f_454_ = crate::leanh::lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_454_, 0, v_toPure_453_);
    crate::leanh::lean_closure_set(v___f_454_, 1, v___y_450_);
    crate::leanh::lean_closure_set(v___f_454_, 2, v_toBind_452_);
    crate::leanh::lean_closure_set(v___f_454_, 3, v_lift_445_);
    v___x_455_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_454_,
        v_it_448_,
        v_init_449_,
        crate::leanh::lean_box(0),
    );
    return v___x_455_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg(
    mut v_inst_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_457_ = crate::leanh::lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_457_, 0, v_inst_456_);
    return v___f_457_;
}
pub unsafe fn l_instIteratorLoopSubarrayIteratorIdOfMonad(
    mut v_00_u03b1_458_: *mut crate::leanh::LeanObject,
    mut v_m_459_: *mut crate::leanh::LeanObject,
    mut v_inst_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_461_ = crate::leanh::lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_461_, 0, v_inst_460_);
    return v___f_461_;
}
pub unsafe fn l_Subarray_instToIterator___lam__0(
    mut v_x_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_462_);
    return v_x_462_;
}
pub unsafe fn l_Subarray_instToIterator___lam__0___boxed(
    mut v_x_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Subarray_instToIterator___lam__0(v_x_463_);
    crate::leanh::lean_dec_ref(v_x_463_);
    return v_res_464_;
}
pub unsafe fn l_Subarray_instToIterator(
    mut v_00_u03b1_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_467_ = l_Subarray_instToIterator___closed__0;
    return v___f_467_;
}
pub unsafe fn l_instForInSubarrayOfMonad___redArg(
    mut v_inst_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_469_ = l_Subarray_instToIterator___closed__0;
    crate::leanh::lean_inc_ref(v_inst_468_);
    v___f_470_ = crate::leanh::lean_alloc_closure(
        l_instIteratorLoopSubarrayIteratorIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_470_, 0, v_inst_468_);
    v___x_471_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(
        v_inst_468_,
        v___f_469_,
        v___f_470_,
    );
    return v___x_471_;
}
pub unsafe fn l_instForInSubarrayOfMonad(
    mut v_00_u03b1_472_: *mut crate::leanh::LeanObject,
    mut v_m_473_: *mut crate::leanh::LeanObject,
    mut v_inst_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_475_ = l_instForInSubarrayOfMonad___redArg(v_inst_474_);
    return v___x_475_;
}
pub unsafe fn l_Subarray_forIn___redArg___lam__0(
    mut v_toPure_476_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_478_ = crate::leanh::lean_apply_2(
        v_toPure_476_,
        crate::leanh::lean_box(0),
        v_____do__lift_477_,
    );
    return v___x_478_;
}
pub unsafe fn l_Subarray_forIn___redArg___lam__1(
    mut v_toPure_479_: *mut crate::leanh::LeanObject,
    mut v_recur_480_: *mut crate::leanh::LeanObject,
    mut v___x_481_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_482_) == 0 {
        let mut v_a_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_481_);
        crate::leanh::lean_dec(v_recur_480_);
        v_a_483_ = crate::leanh::lean_ctor_get(v_____do__lift_482_, 0);
        crate::leanh::lean_inc(v_a_483_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_484_ = crate::leanh::lean_apply_2(v_toPure_479_, crate::leanh::lean_box(0), v_a_483_);
        return v___x_484_;
    } else {
        let mut v_a_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_479_);
        v_a_485_ = crate::leanh::lean_ctor_get(v_____do__lift_482_, 0);
        crate::leanh::lean_inc(v_a_485_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_482_, 1);
        v___x_486_ = crate::leanh::lean_apply_4(
            v_recur_480_,
            v___x_481_,
            v_a_485_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_486_;
    }
}
pub unsafe fn l_Subarray_forIn___redArg___lam__2(
    mut v_toPure_487_: *mut crate::leanh::LeanObject,
    mut v_f_488_: *mut crate::leanh::LeanObject,
    mut v_toBind_489_: *mut crate::leanh::LeanObject,
    mut v___f_490_: *mut crate::leanh::LeanObject,
    mut v_it_491_: *mut crate::leanh::LeanObject,
    mut v_acc_492_: *mut crate::leanh::LeanObject,
    mut v_hP_493_: *mut crate::leanh::LeanObject,
    mut v_recur_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_495_ = crate::leanh::lean_ctor_get(v_it_491_, 0);
                v_start_496_ = crate::leanh::lean_ctor_get(v_it_491_, 1);
                v_stop_497_ = crate::leanh::lean_ctor_get(v_it_491_, 2);
                v_isSharedCheck_513_ = (!crate::leanh::lean_is_exclusive(v_it_491_)) as u8;
                if v_isSharedCheck_513_ == 0 {
                    v___x_499_ = v_it_491_;
                    v_isShared_500_ = v_isSharedCheck_513_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_497_);
                    crate::leanh::lean_inc(v_start_496_);
                    crate::leanh::lean_inc(v_array_495_);
                    crate::leanh::lean_dec(v_it_491_);
                    v___x_499_ = crate::leanh::lean_box(0);
                    v_isShared_500_ = v_isSharedCheck_513_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_501_ = lean_nat_dec_lt(v_start_496_, v_stop_497_);
                if v___x_501_ == 0 {
                    crate::leanh::lean_del_object(v___x_499_);
                    crate::leanh::lean_dec(v_stop_497_);
                    crate::leanh::lean_dec(v_start_496_);
                    crate::leanh::lean_dec_ref(v_array_495_);
                    crate::leanh::lean_dec(v_recur_494_);
                    crate::leanh::lean_dec(v___f_490_);
                    crate::leanh::lean_dec(v_toBind_489_);
                    crate::leanh::lean_dec(v_f_488_);
                    v___x_502_ = crate::leanh::lean_apply_2(
                        v_toPure_487_,
                        crate::leanh::lean_box(0),
                        v_acc_492_,
                    );
                    return v___x_502_;
                } else {
                    v___x_503_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_504_ = lean_nat_add(v_start_496_, v___x_503_);
                    crate::leanh::lean_inc_ref(v_array_495_);
                    if v_isShared_500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_499_, 1, v___x_504_);
                        v___x_506_ = v___x_499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_512_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_512_, 0, v_array_495_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_504_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_512_, 2, v_stop_497_);
                        v___x_506_ = v_reuseFailAlloc_512_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___f_507_ = crate::leanh::lean_alloc_closure(
                    l_Subarray_forIn___redArg___lam__1 as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_507_, 0, v_toPure_487_);
                crate::leanh::lean_closure_set(v___f_507_, 1, v_recur_494_);
                crate::leanh::lean_closure_set(v___f_507_, 2, v___x_506_);
                v___x_508_ = lean_array_fget(v_array_495_, v_start_496_);
                crate::leanh::lean_dec(v_start_496_);
                crate::leanh::lean_dec_ref(v_array_495_);
                v___x_509_ = crate::leanh::lean_apply_2(v_f_488_, v___x_508_, v_acc_492_);
                crate::leanh::lean_inc(v_toBind_489_);
                v___x_510_ = crate::leanh::lean_apply_4(
                    v_toBind_489_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_509_,
                    v___f_490_,
                );
                v___x_511_ = crate::leanh::lean_apply_4(
                    v_toBind_489_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_inst_514_: *mut crate::leanh::LeanObject,
    mut v_s_515_: *mut crate::leanh::LeanObject,
    mut v_b_516_: *mut crate::leanh::LeanObject,
    mut v_f_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_518_ = crate::leanh::lean_ctor_get(v_inst_514_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_518_);
    v_toBind_519_ = crate::leanh::lean_ctor_get(v_inst_514_, 1);
    crate::leanh::lean_inc(v_toBind_519_);
    crate::leanh::lean_dec_ref(v_inst_514_);
    v_toPure_520_ = crate::leanh::lean_ctor_get(v_toApplicative_518_, 1);
    crate::leanh::lean_inc_n(v_toPure_520_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_518_);
    v___f_521_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_521_, 0, v_toPure_520_);
    v___f_522_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_522_, 0, v_toPure_520_);
    crate::leanh::lean_closure_set(v___f_522_, 1, v_f_517_);
    crate::leanh::lean_closure_set(v___f_522_, 2, v_toBind_519_);
    crate::leanh::lean_closure_set(v___f_522_, 3, v___f_521_);
    v___x_523_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_522_,
        v_s_515_,
        v_b_516_,
        crate::leanh::lean_box(0),
    );
    return v___x_523_;
}
pub unsafe fn l_Subarray_forIn(
    mut v_00_u03b1_524_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_525_: *mut crate::leanh::LeanObject,
    mut v_m_526_: *mut crate::leanh::LeanObject,
    mut v_inst_527_: *mut crate::leanh::LeanObject,
    mut v_s_528_: *mut crate::leanh::LeanObject,
    mut v_b_529_: *mut crate::leanh::LeanObject,
    mut v_f_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_531_ = crate::leanh::lean_ctor_get(v_inst_527_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_531_);
    v_toBind_532_ = crate::leanh::lean_ctor_get(v_inst_527_, 1);
    crate::leanh::lean_inc(v_toBind_532_);
    crate::leanh::lean_dec_ref(v_inst_527_);
    v_toPure_533_ = crate::leanh::lean_ctor_get(v_toApplicative_531_, 1);
    crate::leanh::lean_inc_n(v_toPure_533_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_531_);
    v___f_534_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_534_, 0, v_toPure_533_);
    v___f_535_ = crate::leanh::lean_alloc_closure(
        l_Subarray_forIn___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_535_, 0, v_toPure_533_);
    crate::leanh::lean_closure_set(v___f_535_, 1, v_f_530_);
    crate::leanh::lean_closure_set(v___f_535_, 2, v_toBind_532_);
    crate::leanh::lean_closure_set(v___f_535_, 3, v___f_534_);
    v___x_536_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_535_,
        v_s_528_,
        v_b_529_,
        crate::leanh::lean_box(0),
    );
    return v___x_536_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(
    mut v_a_537_: *mut crate::leanh::LeanObject,
    mut v_b_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_539_ = crate::leanh::lean_ctor_get(v_a_537_, 0);
                v_start_540_ = crate::leanh::lean_ctor_get(v_a_537_, 1);
                v_stop_541_ = crate::leanh::lean_ctor_get(v_a_537_, 2);
                v_isSharedCheck_554_ = (!crate::leanh::lean_is_exclusive(v_a_537_)) as u8;
                if v_isSharedCheck_554_ == 0 {
                    v___x_543_ = v_a_537_;
                    v_isShared_544_ = v_isSharedCheck_554_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_541_);
                    crate::leanh::lean_inc(v_start_540_);
                    crate::leanh::lean_inc(v_array_539_);
                    crate::leanh::lean_dec(v_a_537_);
                    v___x_543_ = crate::leanh::lean_box(0);
                    v_isShared_544_ = v_isSharedCheck_554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_545_ = lean_nat_dec_lt(v_start_540_, v_stop_541_);
                if v___x_545_ == 0 {
                    crate::leanh::lean_del_object(v___x_543_);
                    crate::leanh::lean_dec(v_stop_541_);
                    crate::leanh::lean_dec(v_start_540_);
                    crate::leanh::lean_dec_ref(v_array_539_);
                    return v_b_538_;
                } else {
                    v___x_546_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_547_ = lean_nat_add(v_start_540_, v___x_546_);
                    crate::leanh::lean_inc_ref(v_array_539_);
                    if v_isShared_544_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_543_, 1, v___x_547_);
                        v___x_549_ = v___x_543_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_553_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v_array_539_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_547_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 2, v_stop_541_);
                        v___x_549_ = v_reuseFailAlloc_553_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_550_ = lean_array_fget(v_array_539_, v_start_540_);
                crate::leanh::lean_dec(v_start_540_);
                crate::leanh::lean_dec_ref(v_array_539_);
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
pub unsafe fn l_Subarray_copy___redArg(
    mut v_s_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Subarray_copy___redArg___closed__0;
    v___x_559_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_557_, v___x_558_);
    return v___x_559_;
}
pub unsafe fn l_Subarray_copy(
    mut v_00_u03b1_560_: *mut crate::leanh::LeanObject,
    mut v_s_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Subarray_copy___redArg(v_s_561_);
    return v___x_562_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0(
    mut v_00_u03b1_563_: *mut crate::leanh::LeanObject,
    mut v_inst_564_: *mut crate::leanh::LeanObject,
    mut v_R_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
    mut v_b_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_a_566_, v_b_567_);
    return v___x_568_;
}
pub unsafe fn l_instCoeSubarrayArray(
    mut v_00_u03b1_570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = l_instCoeSubarrayArray___closed__0;
    return v___x_571_;
}
pub unsafe fn l_Array_ofSubarray___redArg(
    mut v_s_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Subarray_copy___redArg___closed__0;
    v___x_574_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Subarray_copy_spec__0___redArg(v_s_572_, v___x_573_);
    return v___x_574_;
}
pub unsafe fn l_Array_ofSubarray(
    mut v_00_u03b1_575_: *mut crate::leanh::LeanObject,
    mut v_s_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ = l_Array_ofSubarray___redArg(v_s_576_);
    return v___x_577_;
}
pub unsafe fn l_Array_instAppendSubarray___lam__0(
    mut v_it_578_: *mut crate::leanh::LeanObject,
    mut v_acc_579_: *mut crate::leanh::LeanObject,
    mut v_recur_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_581_ = crate::leanh::lean_ctor_get(v_it_578_, 0);
                v_start_582_ = crate::leanh::lean_ctor_get(v_it_578_, 1);
                v_stop_583_ = crate::leanh::lean_ctor_get(v_it_578_, 2);
                v_isSharedCheck_596_ = (!crate::leanh::lean_is_exclusive(v_it_578_)) as u8;
                if v_isSharedCheck_596_ == 0 {
                    v___x_585_ = v_it_578_;
                    v_isShared_586_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_583_);
                    crate::leanh::lean_inc(v_start_582_);
                    crate::leanh::lean_inc(v_array_581_);
                    crate::leanh::lean_dec(v_it_578_);
                    v___x_585_ = crate::leanh::lean_box(0);
                    v_isShared_586_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_587_ = lean_nat_dec_lt(v_start_582_, v_stop_583_);
                if v___x_587_ == 0 {
                    crate::leanh::lean_del_object(v___x_585_);
                    crate::leanh::lean_dec(v_stop_583_);
                    crate::leanh::lean_dec(v_start_582_);
                    crate::leanh::lean_dec_ref(v_array_581_);
                    crate::leanh::lean_dec_ref(v_recur_580_);
                    return v_acc_579_;
                } else {
                    v___x_588_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_589_ = lean_nat_add(v_start_582_, v___x_588_);
                    crate::leanh::lean_inc_ref(v_array_581_);
                    if v_isShared_586_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_585_, 1, v___x_589_);
                        v___x_591_ = v___x_585_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_595_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_array_581_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_589_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 2, v_stop_583_);
                        v___x_591_ = v_reuseFailAlloc_595_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_592_ = lean_array_fget(v_array_581_, v_start_582_);
                crate::leanh::lean_dec(v_start_582_);
                crate::leanh::lean_dec_ref(v_array_581_);
                v___x_593_ = lean_array_push(v_acc_579_, v___x_592_);
                v___x_594_ = crate::leanh::lean_apply_3(
                    v_recur_580_,
                    v___x_591_,
                    v___x_593_,
                    crate::leanh::lean_box(0),
                );
                return v___x_594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_instAppendSubarray___lam__2(
    mut v___f_597_: *mut crate::leanh::LeanObject,
    mut v___f_598_: *mut crate::leanh::LeanObject,
    mut v_x_599_: *mut crate::leanh::LeanObject,
    mut v_y_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_602_ = l_Subarray_copy___redArg___closed__0;
    v___x_603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_597_, v_x_599_, v___x_602_,
    );
    v___x_604_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_598_, v_y_600_, v___x_602_,
    );
    v_a_605_ = l_Array_append___redArg(v___x_603_, v___x_604_);
    crate::leanh::lean_dec(v___x_604_);
    v___x_606_ = lean_array_get_size(v_a_605_);
    v___x_607_ = l_Array_toSubarray___redArg(v_a_605_, v___x_601_, v___x_606_);
    return v___x_607_;
}
pub unsafe fn l_Array_instAppendSubarray(
    mut v_00_u03b1_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_612_ = l_Array_instAppendSubarray___closed__1;
    return v___f_612_;
}
pub unsafe fn l_Array_Subarray_repr___redArg(
    mut v_inst_616_: *mut crate::leanh::LeanObject,
    mut v_s_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_618_ = l_Array_instAppendSubarray___closed__0;
    v___x_619_ = l_Subarray_copy___redArg___closed__0;
    v___x_620_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_618_, v_s_617_, v___x_619_,
    );
    v___x_621_ = l_Array_repr___redArg(v_inst_616_, v___x_620_);
    v___x_622_ = l_Array_Subarray_repr___redArg___closed__1;
    v___x_623_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_623_, 0, v___x_621_);
    crate::leanh::lean_ctor_set(v___x_623_, 1, v___x_622_);
    return v___x_623_;
}
pub unsafe fn l_Array_Subarray_repr(
    mut v_00_u03b1_624_: *mut crate::leanh::LeanObject,
    mut v_inst_625_: *mut crate::leanh::LeanObject,
    mut v_s_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = l_Array_Subarray_repr___redArg(v_inst_625_, v_s_626_);
    return v___x_627_;
}
pub unsafe fn l_Array_instReprSubarray___redArg___lam__0(
    mut v_inst_628_: *mut crate::leanh::LeanObject,
    mut v_s_629_: *mut crate::leanh::LeanObject,
    mut v_x_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Array_Subarray_repr___redArg(v_inst_628_, v_s_629_);
    return v___x_631_;
}
pub unsafe fn l_Array_instReprSubarray___redArg___lam__0___boxed(
    mut v_inst_632_: *mut crate::leanh::LeanObject,
    mut v_s_633_: *mut crate::leanh::LeanObject,
    mut v_x_634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Array_instReprSubarray___redArg___lam__0(v_inst_632_, v_s_633_, v_x_634_);
    crate::leanh::lean_dec(v_x_634_);
    return v_res_635_;
}
pub unsafe fn l_Array_instReprSubarray___redArg(
    mut v_inst_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_637_ = crate::leanh::lean_alloc_closure(
        l_Array_instReprSubarray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_637_, 0, v_inst_636_);
    return v___f_637_;
}
pub unsafe fn l_Array_instReprSubarray(
    mut v_00_u03b1_638_: *mut crate::leanh::LeanObject,
    mut v_inst_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_640_ = crate::leanh::lean_alloc_closure(
        l_Array_instReprSubarray___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_640_, 0, v_inst_639_);
    return v___f_640_;
}
pub unsafe fn l_Array_instToStringSubarray___redArg___lam__1(
    mut v___f_642_: *mut crate::leanh::LeanObject,
    mut v_inst_643_: *mut crate::leanh::LeanObject,
    mut v_s_644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_645_ = l_Subarray_copy___redArg___closed__0;
    v___x_646_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_642_, v_s_644_, v___x_645_,
    );
    v___x_647_ = l_Array_instToStringSubarray___redArg___lam__1___closed__0;
    v___x_648_ = lean_array_to_list(v___x_646_);
    v___x_649_ = l_List_toString___redArg(v_inst_643_, v___x_648_);
    v___x_650_ = lean_string_append(v___x_647_, v___x_649_);
    crate::leanh::lean_dec_ref(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_Array_instToStringSubarray___redArg(
    mut v_inst_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_652_ = l_Array_instAppendSubarray___closed__0;
    v___f_653_ = crate::leanh::lean_alloc_closure(
        l_Array_instToStringSubarray___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_653_, 0, v___f_652_);
    crate::leanh::lean_closure_set(v___f_653_, 1, v_inst_651_);
    return v___f_653_;
}
pub unsafe fn l_Array_instToStringSubarray(
    mut v_00_u03b1_654_: *mut crate::leanh::LeanObject,
    mut v_inst_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = l_Array_instToStringSubarray___redArg(v_inst_655_);
    return v___x_656_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Array_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Array_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Slice_Array_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Operations(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Array_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_Array_Iterator(builtin);
}
