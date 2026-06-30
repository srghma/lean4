// Lean compiler output
// Module: Init.Data.Slice.Array.Basic
// Imports: Init.Data.Array.Subarray Init.Data.Slice.Notation Init.Data.Range.Polymorphic.Nat
use crate::ffi::{lean_array_get_size, lean_nat_add, lean_nat_dec_le, lean_nat_sub};
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, l_Array_toSubarray___redArg,
    runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Slice::Notation::{
    initialize_Init_Data_Slice_Notation, runtime_initialize_Init_Data_Slice_Notation,
};
pub static l_instSliceableArrayNatSubarray___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableArrayNatSubarray___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableArrayNatSubarray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__1___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__1___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__2___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__2___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__3___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__3___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__4___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__4___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__5___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__5___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__6___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__6___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__7___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__7___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableArrayNatSubarray__8___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableArrayNatSubarray__8___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableArrayNatSubarray__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableArrayNatSubarray__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__1___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__2___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__3___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__4___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__4___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__5___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__6___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__7___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__7___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableSubarrayNat__8___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableSubarrayNat__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableSubarrayNat__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableSubarrayNat__8___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_instSliceableArrayNatSubarray___lam__0(
    mut v_xs_285_: *mut leanh::LeanObject,
    mut v_range_286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_287_ = leanh::lean_ctor_get(v_range_286_, 0);
    leanh::lean_inc(v_lower_287_);
    v_upper_288_ = leanh::lean_ctor_get(v_range_286_, 1);
    leanh::lean_inc(v_upper_288_);
    leanh::lean_dec_ref(v_range_286_);
    v___x_289_ = leanh::lean_unsigned_to_nat(1);
    v___x_290_ = lean_nat_add(v_upper_288_, v___x_289_);
    leanh::lean_dec(v_upper_288_);
    v___x_291_ = l_Array_toSubarray___redArg(v_xs_285_, v_lower_287_, v___x_290_);
    return v___x_291_;
}
pub unsafe fn l_instSliceableArrayNatSubarray(
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_294_ = l_instSliceableArrayNatSubarray___closed__0;
    return v___f_294_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__1___lam__0(
    mut v_xs_295_: *mut leanh::LeanObject,
    mut v_range_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_297_ = leanh::lean_ctor_get(v_range_296_, 0);
    leanh::lean_inc(v_lower_297_);
    v_upper_298_ = leanh::lean_ctor_get(v_range_296_, 1);
    leanh::lean_inc(v_upper_298_);
    leanh::lean_dec_ref(v_range_296_);
    v___x_299_ = l_Array_toSubarray___redArg(v_xs_295_, v_lower_297_, v_upper_298_);
    return v___x_299_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__1(
    mut v_00_u03b1_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_302_ = l_instSliceableArrayNatSubarray__1___closed__0;
    return v___f_302_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__2___lam__0(
    mut v_xs_303_: *mut leanh::LeanObject,
    mut v_range_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: u8 = 0;
    v___x_305_ = leanh::lean_unsigned_to_nat(0);
    v___x_306_ = lean_array_get_size(v_xs_303_);
    v___x_307_ = lean_nat_dec_le(v_range_304_, v___x_305_);
    if v___x_307_ == 0 {
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_308_ = l_Array_toSubarray___redArg(v_xs_303_, v_range_304_, v___x_306_);
        return v___x_308_;
    } else {
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_range_304_);
        v___x_309_ = l_Array_toSubarray___redArg(v_xs_303_, v___x_305_, v___x_306_);
        return v___x_309_;
    }
}
pub unsafe fn l_instSliceableArrayNatSubarray__2(
    mut v_00_u03b1_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_312_ = l_instSliceableArrayNatSubarray__2___closed__0;
    return v___f_312_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__3___lam__0(
    mut v_xs_313_: *mut leanh::LeanObject,
    mut v_range_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_315_ = leanh::lean_ctor_get(v_range_314_, 0);
    v_upper_316_ = leanh::lean_ctor_get(v_range_314_, 1);
    v___x_317_ = leanh::lean_unsigned_to_nat(1);
    v___x_318_ = lean_nat_add(v_lower_315_, v___x_317_);
    v___x_319_ = lean_nat_add(v_upper_316_, v___x_317_);
    v___x_320_ = l_Array_toSubarray___redArg(v_xs_313_, v___x_318_, v___x_319_);
    return v___x_320_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__3___lam__0___boxed(
    mut v_xs_321_: *mut leanh::LeanObject,
    mut v_range_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_323_ = l_instSliceableArrayNatSubarray__3___lam__0(v_xs_321_, v_range_322_);
    leanh::lean_dec_ref(v_range_322_);
    return v_res_323_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__3(
    mut v_00_u03b1_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_326_ = l_instSliceableArrayNatSubarray__3___closed__0;
    return v___f_326_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__4___lam__0(
    mut v_xs_327_: *mut leanh::LeanObject,
    mut v_range_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_329_ = leanh::lean_ctor_get(v_range_328_, 0);
    leanh::lean_inc(v_lower_329_);
    v_upper_330_ = leanh::lean_ctor_get(v_range_328_, 1);
    leanh::lean_inc(v_upper_330_);
    leanh::lean_dec_ref(v_range_328_);
    v___x_331_ = leanh::lean_unsigned_to_nat(1);
    v___x_332_ = lean_nat_add(v_lower_329_, v___x_331_);
    leanh::lean_dec(v_lower_329_);
    v___x_333_ = l_Array_toSubarray___redArg(v_xs_327_, v___x_332_, v_upper_330_);
    return v___x_333_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__4(
    mut v_00_u03b1_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_336_ = l_instSliceableArrayNatSubarray__4___closed__0;
    return v___f_336_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__5___lam__0(
    mut v_xs_337_: *mut leanh::LeanObject,
    mut v_range_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: u8 = 0;
    v___x_339_ = leanh::lean_unsigned_to_nat(0);
    v___x_340_ = lean_array_get_size(v_xs_337_);
    v___x_341_ = leanh::lean_unsigned_to_nat(1);
    v___x_342_ = lean_nat_add(v_range_338_, v___x_341_);
    v___x_343_ = lean_nat_dec_le(v___x_342_, v___x_339_);
    if v___x_343_ == 0 {
        let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_344_ = l_Array_toSubarray___redArg(v_xs_337_, v___x_342_, v___x_340_);
        return v___x_344_;
    } else {
        let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_342_);
        v___x_345_ = l_Array_toSubarray___redArg(v_xs_337_, v___x_339_, v___x_340_);
        return v___x_345_;
    }
}
pub unsafe fn l_instSliceableArrayNatSubarray__5___lam__0___boxed(
    mut v_xs_346_: *mut leanh::LeanObject,
    mut v_range_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_instSliceableArrayNatSubarray__5___lam__0(v_xs_346_, v_range_347_);
    leanh::lean_dec(v_range_347_);
    return v_res_348_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__5(
    mut v_00_u03b1_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_351_ = l_instSliceableArrayNatSubarray__5___closed__0;
    return v___f_351_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__6___lam__0(
    mut v_xs_352_: *mut leanh::LeanObject,
    mut v_range_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_354_ = leanh::lean_unsigned_to_nat(0);
    v___x_355_ = leanh::lean_unsigned_to_nat(1);
    v___x_356_ = lean_nat_add(v_range_353_, v___x_355_);
    v___x_357_ = l_Array_toSubarray___redArg(v_xs_352_, v___x_354_, v___x_356_);
    return v___x_357_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__6___lam__0___boxed(
    mut v_xs_358_: *mut leanh::LeanObject,
    mut v_range_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_instSliceableArrayNatSubarray__6___lam__0(v_xs_358_, v_range_359_);
    leanh::lean_dec(v_range_359_);
    return v_res_360_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__6(
    mut v_00_u03b1_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_363_ = l_instSliceableArrayNatSubarray__6___closed__0;
    return v___f_363_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__7___lam__0(
    mut v_xs_364_: *mut leanh::LeanObject,
    mut v_range_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_366_ = leanh::lean_unsigned_to_nat(0);
    v___x_367_ = l_Array_toSubarray___redArg(v_xs_364_, v___x_366_, v_range_365_);
    return v___x_367_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__7(
    mut v_00_u03b1_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_370_ = l_instSliceableArrayNatSubarray__7___closed__0;
    return v___f_370_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__8___lam__0(
    mut v_xs_371_: *mut leanh::LeanObject,
    mut v_x_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_unsigned_to_nat(0);
    v___x_374_ = lean_array_get_size(v_xs_371_);
    v___x_375_ = l_Array_toSubarray___redArg(v_xs_371_, v___x_373_, v___x_374_);
    return v___x_375_;
}
pub unsafe fn l_instSliceableArrayNatSubarray__8(
    mut v_00_u03b1_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_378_ = l_instSliceableArrayNatSubarray__8___closed__0;
    return v___f_378_;
}
pub unsafe fn l_instSliceableSubarrayNat___lam__0(
    mut v_xs_379_: *mut leanh::LeanObject,
    mut v_range_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u8 = 0;
    let mut v___x_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_381_ = leanh::lean_ctor_get(v_xs_379_, 0);
                leanh::lean_inc_ref(v_array_381_);
                v_start_382_ = leanh::lean_ctor_get(v_xs_379_, 1);
                leanh::lean_inc(v_start_382_);
                v_stop_383_ = leanh::lean_ctor_get(v_xs_379_, 2);
                leanh::lean_inc(v_stop_383_);
                leanh::lean_dec_ref(v_xs_379_);
                v_lower_390_ = leanh::lean_ctor_get(v_range_380_, 0);
                v_upper_391_ = leanh::lean_ctor_get(v_range_380_, 1);
                v___x_392_ = leanh::lean_unsigned_to_nat(0);
                v___x_393_ = lean_nat_sub(v_stop_383_, v_start_382_);
                leanh::lean_dec(v_stop_383_);
                v___x_399_ = lean_nat_dec_le(v_lower_390_, v___x_392_);
                if v___x_399_ == 0 {
                    v___y_395_ = v_lower_390_;
                    state = 2;
                    continue;
                } else {
                    v___y_395_ = v___x_392_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_387_ = lean_nat_add(v_lower_385_, v_start_382_);
                v___x_388_ = lean_nat_add(v_upper_386_, v_start_382_);
                leanh::lean_dec(v_start_382_);
                leanh::lean_dec(v_upper_386_);
                v___x_389_ = l_Array_toSubarray___redArg(v_array_381_, v___x_387_, v___x_388_);
                return v___x_389_;
            }
            2 => {
                v___x_396_ = leanh::lean_unsigned_to_nat(1);
                v___x_397_ = lean_nat_add(v_upper_391_, v___x_396_);
                v___x_398_ = lean_nat_dec_le(v___x_397_, v___x_393_);
                if v___x_398_ == 0 {
                    leanh::lean_dec(v___x_397_);
                    v_lower_385_ = v___y_395_;
                    v_upper_386_ = v___x_393_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_393_);
                    v_lower_385_ = v___y_395_;
                    v_upper_386_ = v___x_397_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat___lam__0___boxed(
    mut v_xs_400_: *mut leanh::LeanObject,
    mut v_range_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_402_ = l_instSliceableSubarrayNat___lam__0(v_xs_400_, v_range_401_);
    leanh::lean_dec_ref(v_range_401_);
    return v_res_402_;
}
pub unsafe fn l_instSliceableSubarrayNat(
    mut v_00_u03b1_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_405_ = l_instSliceableSubarrayNat___closed__0;
    return v___f_405_;
}
pub unsafe fn l_instSliceableSubarrayNat__1___lam__0(
    mut v_xs_406_: *mut leanh::LeanObject,
    mut v_range_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u8 = 0;
    let mut v___x_424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_408_ = leanh::lean_ctor_get(v_xs_406_, 0);
                leanh::lean_inc_ref(v_array_408_);
                v_start_409_ = leanh::lean_ctor_get(v_xs_406_, 1);
                leanh::lean_inc(v_start_409_);
                v_stop_410_ = leanh::lean_ctor_get(v_xs_406_, 2);
                leanh::lean_inc(v_stop_410_);
                leanh::lean_dec_ref(v_xs_406_);
                v_lower_417_ = leanh::lean_ctor_get(v_range_407_, 0);
                leanh::lean_inc(v_lower_417_);
                v_upper_418_ = leanh::lean_ctor_get(v_range_407_, 1);
                leanh::lean_inc(v_upper_418_);
                leanh::lean_dec_ref(v_range_407_);
                v___x_419_ = leanh::lean_unsigned_to_nat(0);
                v___x_420_ = lean_nat_sub(v_stop_410_, v_start_409_);
                leanh::lean_dec(v_stop_410_);
                v___x_424_ = lean_nat_dec_le(v_lower_417_, v___x_419_);
                if v___x_424_ == 0 {
                    v___y_422_ = v_lower_417_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_lower_417_);
                    v___y_422_ = v___x_419_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_414_ = lean_nat_add(v_lower_412_, v_start_409_);
                leanh::lean_dec(v_lower_412_);
                v___x_415_ = lean_nat_add(v_upper_413_, v_start_409_);
                leanh::lean_dec(v_start_409_);
                leanh::lean_dec(v_upper_413_);
                v___x_416_ = l_Array_toSubarray___redArg(v_array_408_, v___x_414_, v___x_415_);
                return v___x_416_;
            }
            2 => {
                v___x_423_ = lean_nat_dec_le(v_upper_418_, v___x_420_);
                if v___x_423_ == 0 {
                    leanh::lean_dec(v_upper_418_);
                    v_lower_412_ = v___y_422_;
                    v_upper_413_ = v___x_420_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_420_);
                    v_lower_412_ = v___y_422_;
                    v_upper_413_ = v_upper_418_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__1(
    mut v_00_u03b1_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_427_ = l_instSliceableSubarrayNat__1___closed__0;
    return v___f_427_;
}
pub unsafe fn l_instSliceableSubarrayNat__2___lam__0(
    mut v_xs_428_: *mut leanh::LeanObject,
    mut v_range_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_430_ = leanh::lean_ctor_get(v_xs_428_, 0);
                leanh::lean_inc_ref(v_array_430_);
                v_start_431_ = leanh::lean_ctor_get(v_xs_428_, 1);
                leanh::lean_inc(v_start_431_);
                v_stop_432_ = leanh::lean_ctor_get(v_xs_428_, 2);
                leanh::lean_inc(v_stop_432_);
                leanh::lean_dec_ref(v_xs_428_);
                v___x_439_ = leanh::lean_unsigned_to_nat(0);
                v___x_440_ = lean_nat_sub(v_stop_432_, v_start_431_);
                leanh::lean_dec(v_stop_432_);
                v___x_441_ = lean_nat_dec_le(v_range_429_, v___x_439_);
                if v___x_441_ == 0 {
                    v_lower_434_ = v_range_429_;
                    v_upper_435_ = v___x_440_;
                    state = 1;
                    continue;
                } else {
                    v_lower_434_ = v___x_439_;
                    v_upper_435_ = v___x_440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_436_ = lean_nat_add(v_lower_434_, v_start_431_);
                v___x_437_ = lean_nat_add(v_upper_435_, v_start_431_);
                leanh::lean_dec(v_start_431_);
                leanh::lean_dec(v_upper_435_);
                v___x_438_ = l_Array_toSubarray___redArg(v_array_430_, v___x_436_, v___x_437_);
                return v___x_438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__2___lam__0___boxed(
    mut v_xs_442_: *mut leanh::LeanObject,
    mut v_range_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_444_ = l_instSliceableSubarrayNat__2___lam__0(v_xs_442_, v_range_443_);
    leanh::lean_dec(v_range_443_);
    return v_res_444_;
}
pub unsafe fn l_instSliceableSubarrayNat__2(
    mut v_00_u03b1_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_447_ = l_instSliceableSubarrayNat__2___closed__0;
    return v___f_447_;
}
pub unsafe fn l_instSliceableSubarrayNat__3___lam__0(
    mut v_xs_448_: *mut leanh::LeanObject,
    mut v_range_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_450_ = leanh::lean_ctor_get(v_xs_448_, 0);
                leanh::lean_inc_ref(v_array_450_);
                v_start_451_ = leanh::lean_ctor_get(v_xs_448_, 1);
                leanh::lean_inc(v_start_451_);
                v_stop_452_ = leanh::lean_ctor_get(v_xs_448_, 2);
                leanh::lean_inc(v_stop_452_);
                leanh::lean_dec_ref(v_xs_448_);
                v_lower_459_ = leanh::lean_ctor_get(v_range_449_, 0);
                v_upper_460_ = leanh::lean_ctor_get(v_range_449_, 1);
                v___x_461_ = leanh::lean_unsigned_to_nat(0);
                v___x_462_ = lean_nat_sub(v_stop_452_, v_start_451_);
                leanh::lean_dec(v_stop_452_);
                v___x_463_ = leanh::lean_unsigned_to_nat(1);
                v___x_468_ = lean_nat_add(v_lower_459_, v___x_463_);
                v___x_469_ = lean_nat_dec_le(v___x_468_, v___x_461_);
                if v___x_469_ == 0 {
                    v___y_465_ = v___x_468_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_468_);
                    v___y_465_ = v___x_461_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_456_ = lean_nat_add(v_lower_454_, v_start_451_);
                leanh::lean_dec(v_lower_454_);
                v___x_457_ = lean_nat_add(v_upper_455_, v_start_451_);
                leanh::lean_dec(v_start_451_);
                leanh::lean_dec(v_upper_455_);
                v___x_458_ = l_Array_toSubarray___redArg(v_array_450_, v___x_456_, v___x_457_);
                return v___x_458_;
            }
            2 => {
                v___x_466_ = lean_nat_add(v_upper_460_, v___x_463_);
                v___x_467_ = lean_nat_dec_le(v___x_466_, v___x_462_);
                if v___x_467_ == 0 {
                    leanh::lean_dec(v___x_466_);
                    v_lower_454_ = v___y_465_;
                    v_upper_455_ = v___x_462_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_462_);
                    v_lower_454_ = v___y_465_;
                    v_upper_455_ = v___x_466_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__3___lam__0___boxed(
    mut v_xs_470_: *mut leanh::LeanObject,
    mut v_range_471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_472_ = l_instSliceableSubarrayNat__3___lam__0(v_xs_470_, v_range_471_);
    leanh::lean_dec_ref(v_range_471_);
    return v_res_472_;
}
pub unsafe fn l_instSliceableSubarrayNat__3(
    mut v_00_u03b1_474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_475_ = l_instSliceableSubarrayNat__3___closed__0;
    return v___f_475_;
}
pub unsafe fn l_instSliceableSubarrayNat__4___lam__0(
    mut v_xs_476_: *mut leanh::LeanObject,
    mut v_range_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_478_ = leanh::lean_ctor_get(v_xs_476_, 0);
                leanh::lean_inc_ref(v_array_478_);
                v_start_479_ = leanh::lean_ctor_get(v_xs_476_, 1);
                leanh::lean_inc(v_start_479_);
                v_stop_480_ = leanh::lean_ctor_get(v_xs_476_, 2);
                leanh::lean_inc(v_stop_480_);
                leanh::lean_dec_ref(v_xs_476_);
                v_lower_487_ = leanh::lean_ctor_get(v_range_477_, 0);
                leanh::lean_inc(v_lower_487_);
                v_upper_488_ = leanh::lean_ctor_get(v_range_477_, 1);
                leanh::lean_inc(v_upper_488_);
                leanh::lean_dec_ref(v_range_477_);
                v___x_489_ = leanh::lean_unsigned_to_nat(0);
                v___x_490_ = lean_nat_sub(v_stop_480_, v_start_479_);
                leanh::lean_dec(v_stop_480_);
                v___x_494_ = leanh::lean_unsigned_to_nat(1);
                v___x_495_ = lean_nat_add(v_lower_487_, v___x_494_);
                leanh::lean_dec(v_lower_487_);
                v___x_496_ = lean_nat_dec_le(v___x_495_, v___x_489_);
                if v___x_496_ == 0 {
                    v___y_492_ = v___x_495_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_495_);
                    v___y_492_ = v___x_489_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_484_ = lean_nat_add(v_lower_482_, v_start_479_);
                leanh::lean_dec(v_lower_482_);
                v___x_485_ = lean_nat_add(v_upper_483_, v_start_479_);
                leanh::lean_dec(v_start_479_);
                leanh::lean_dec(v_upper_483_);
                v___x_486_ = l_Array_toSubarray___redArg(v_array_478_, v___x_484_, v___x_485_);
                return v___x_486_;
            }
            2 => {
                v___x_493_ = lean_nat_dec_le(v_upper_488_, v___x_490_);
                if v___x_493_ == 0 {
                    leanh::lean_dec(v_upper_488_);
                    v_lower_482_ = v___y_492_;
                    v_upper_483_ = v___x_490_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_490_);
                    v_lower_482_ = v___y_492_;
                    v_upper_483_ = v_upper_488_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__4(
    mut v_00_u03b1_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_499_ = l_instSliceableSubarrayNat__4___closed__0;
    return v___f_499_;
}
pub unsafe fn l_instSliceableSubarrayNat__5___lam__0(
    mut v_xs_500_: *mut leanh::LeanObject,
    mut v_range_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_502_ = leanh::lean_ctor_get(v_xs_500_, 0);
                leanh::lean_inc_ref(v_array_502_);
                v_start_503_ = leanh::lean_ctor_get(v_xs_500_, 1);
                leanh::lean_inc(v_start_503_);
                v_stop_504_ = leanh::lean_ctor_get(v_xs_500_, 2);
                leanh::lean_inc(v_stop_504_);
                leanh::lean_dec_ref(v_xs_500_);
                v___x_511_ = leanh::lean_unsigned_to_nat(0);
                v___x_512_ = lean_nat_sub(v_stop_504_, v_start_503_);
                leanh::lean_dec(v_stop_504_);
                v___x_513_ = leanh::lean_unsigned_to_nat(1);
                v___x_514_ = lean_nat_add(v_range_501_, v___x_513_);
                v___x_515_ = lean_nat_dec_le(v___x_514_, v___x_511_);
                if v___x_515_ == 0 {
                    v_lower_506_ = v___x_514_;
                    v_upper_507_ = v___x_512_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_514_);
                    v_lower_506_ = v___x_511_;
                    v_upper_507_ = v___x_512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_508_ = lean_nat_add(v_lower_506_, v_start_503_);
                leanh::lean_dec(v_lower_506_);
                v___x_509_ = lean_nat_add(v_upper_507_, v_start_503_);
                leanh::lean_dec(v_start_503_);
                leanh::lean_dec(v_upper_507_);
                v___x_510_ = l_Array_toSubarray___redArg(v_array_502_, v___x_508_, v___x_509_);
                return v___x_510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__5___lam__0___boxed(
    mut v_xs_516_: *mut leanh::LeanObject,
    mut v_range_517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_518_ = l_instSliceableSubarrayNat__5___lam__0(v_xs_516_, v_range_517_);
    leanh::lean_dec(v_range_517_);
    return v_res_518_;
}
pub unsafe fn l_instSliceableSubarrayNat__5(
    mut v_00_u03b1_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_521_ = l_instSliceableSubarrayNat__5___closed__0;
    return v___f_521_;
}
pub unsafe fn l_instSliceableSubarrayNat__6___lam__0(
    mut v_xs_522_: *mut leanh::LeanObject,
    mut v_range_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_524_ = leanh::lean_ctor_get(v_xs_522_, 0);
                leanh::lean_inc_ref(v_array_524_);
                v_start_525_ = leanh::lean_ctor_get(v_xs_522_, 1);
                leanh::lean_inc(v_start_525_);
                v_stop_526_ = leanh::lean_ctor_get(v_xs_522_, 2);
                leanh::lean_inc(v_stop_526_);
                leanh::lean_dec_ref(v_xs_522_);
                v___x_533_ = leanh::lean_unsigned_to_nat(0);
                v___x_534_ = lean_nat_sub(v_stop_526_, v_start_525_);
                leanh::lean_dec(v_stop_526_);
                v___x_535_ = leanh::lean_unsigned_to_nat(1);
                v___x_536_ = lean_nat_add(v_range_523_, v___x_535_);
                v___x_537_ = lean_nat_dec_le(v___x_536_, v___x_534_);
                if v___x_537_ == 0 {
                    leanh::lean_dec(v___x_536_);
                    v_lower_528_ = v___x_533_;
                    v_upper_529_ = v___x_534_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_534_);
                    v_lower_528_ = v___x_533_;
                    v_upper_529_ = v___x_536_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_530_ = lean_nat_add(v_lower_528_, v_start_525_);
                v___x_531_ = lean_nat_add(v_upper_529_, v_start_525_);
                leanh::lean_dec(v_start_525_);
                leanh::lean_dec(v_upper_529_);
                v___x_532_ = l_Array_toSubarray___redArg(v_array_524_, v___x_530_, v___x_531_);
                return v___x_532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__6___lam__0___boxed(
    mut v_xs_538_: *mut leanh::LeanObject,
    mut v_range_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_instSliceableSubarrayNat__6___lam__0(v_xs_538_, v_range_539_);
    leanh::lean_dec(v_range_539_);
    return v_res_540_;
}
pub unsafe fn l_instSliceableSubarrayNat__6(
    mut v_00_u03b1_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_543_ = l_instSliceableSubarrayNat__6___closed__0;
    return v___f_543_;
}
pub unsafe fn l_instSliceableSubarrayNat__7___lam__0(
    mut v_xs_544_: *mut leanh::LeanObject,
    mut v_range_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_546_ = leanh::lean_ctor_get(v_xs_544_, 0);
                leanh::lean_inc_ref(v_array_546_);
                v_start_547_ = leanh::lean_ctor_get(v_xs_544_, 1);
                leanh::lean_inc(v_start_547_);
                v_stop_548_ = leanh::lean_ctor_get(v_xs_544_, 2);
                leanh::lean_inc(v_stop_548_);
                leanh::lean_dec_ref(v_xs_544_);
                v___x_555_ = leanh::lean_unsigned_to_nat(0);
                v___x_556_ = lean_nat_sub(v_stop_548_, v_start_547_);
                leanh::lean_dec(v_stop_548_);
                v___x_557_ = lean_nat_dec_le(v_range_545_, v___x_556_);
                if v___x_557_ == 0 {
                    leanh::lean_dec(v_range_545_);
                    v_lower_550_ = v___x_555_;
                    v_upper_551_ = v___x_556_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_556_);
                    v_lower_550_ = v___x_555_;
                    v_upper_551_ = v_range_545_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_552_ = lean_nat_add(v_lower_550_, v_start_547_);
                v___x_553_ = lean_nat_add(v_upper_551_, v_start_547_);
                leanh::lean_dec(v_start_547_);
                leanh::lean_dec(v_upper_551_);
                v___x_554_ = l_Array_toSubarray___redArg(v_array_546_, v___x_552_, v___x_553_);
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableSubarrayNat__7(
    mut v_00_u03b1_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_560_ = l_instSliceableSubarrayNat__7___closed__0;
    return v___f_560_;
}
pub unsafe fn l_instSliceableSubarrayNat__8___lam__0(
    mut v_xs_561_: *mut leanh::LeanObject,
    mut v_x_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_561_);
    return v_xs_561_;
}
pub unsafe fn l_instSliceableSubarrayNat__8___lam__0___boxed(
    mut v_xs_563_: *mut leanh::LeanObject,
    mut v_x_564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_565_ = l_instSliceableSubarrayNat__8___lam__0(v_xs_563_, v_x_564_);
    leanh::lean_dec_ref(v_xs_563_);
    return v_res_565_;
}
pub unsafe fn l_instSliceableSubarrayNat__8(
    mut v_00_u03b1_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_568_ = l_instSliceableSubarrayNat__8___closed__0;
    return v___f_568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_Array_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_Array_Basic(
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
pub unsafe fn initialize_Init_Data_Slice_Array_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_Array_Basic(builtin);
}