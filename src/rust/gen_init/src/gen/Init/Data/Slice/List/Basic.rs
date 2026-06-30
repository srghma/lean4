// Lean compiler output
// Module: Init.Data.Slice.List.Basic
// Imports: Init.Data.Slice.Basic Init.Data.Slice.Notation
use crate::ffi::{lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub};
use crate::r#gen::Init::Data::List::Basic::l_List_drop___redArg;
use crate::r#gen::Init::Data::Slice::Basic::{
    initialize_Init_Data_Slice_Basic, runtime_initialize_Init_Data_Slice_Basic,
};
use crate::r#gen::Init::Data::Slice::Notation::{
    initialize_Init_Data_Slice_Notation, runtime_initialize_Init_Data_Slice_Notation,
};
pub static l_List_toSlice___redArg___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_List_toSlice___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_toSlice___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_toSlice___redArg___closed__1_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_List_toSlice___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_List_toSlice___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_toSlice___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListNatListSlice___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListNatListSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__1___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__2___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_List_toUnboundedSlice___redArg___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__3___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__3___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__4___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__4___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__5___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__5___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__6___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__6___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__7___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__7___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListNatListSlice__8___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_instSliceableListNatListSlice__8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__1___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__2___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__3___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__4___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__4___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__5___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__6___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__7___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__7___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instSliceableListSliceNat__8___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__8___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_List_toSlice___redArg(
    mut v_as_301_: *mut leanh::LeanObject,
    mut v_start_302_: *mut leanh::LeanObject,
    mut v_stop_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_304_: u8 = 0;
    v___x_304_ = lean_nat_dec_lt(v_start_302_, v_stop_303_);
    if v___x_304_ == 0 {
        let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_start_302_);
        v___x_305_ = l_List_toSlice___redArg___closed__1;
        return v___x_305_;
    } else {
        let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_start_302_);
        v___x_306_ = l_List_drop___redArg(v_start_302_, v_as_301_);
        v___x_307_ = lean_nat_sub(v_stop_303_, v_start_302_);
        leanh::lean_dec(v_start_302_);
        v___x_308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
        v___x_309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_309_, 0, v___x_306_);
        leanh::lean_ctor_set(v___x_309_, 1, v___x_308_);
        return v___x_309_;
    }
}
pub unsafe fn l_List_toSlice___redArg___boxed(
    mut v_as_310_: *mut leanh::LeanObject,
    mut v_start_311_: *mut leanh::LeanObject,
    mut v_stop_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_List_toSlice___redArg(v_as_310_, v_start_311_, v_stop_312_);
    leanh::lean_dec(v_stop_312_);
    leanh::lean_dec(v_as_310_);
    return v_res_313_;
}
pub unsafe fn l_List_toSlice(
    mut v_00_u03b1_314_: *mut leanh::LeanObject,
    mut v_as_315_: *mut leanh::LeanObject,
    mut v_start_316_: *mut leanh::LeanObject,
    mut v_stop_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l_List_toSlice___redArg(v_as_315_, v_start_316_, v_stop_317_);
    return v___x_318_;
}
pub unsafe fn l_List_toSlice___boxed(
    mut v_00_u03b1_319_: *mut leanh::LeanObject,
    mut v_as_320_: *mut leanh::LeanObject,
    mut v_start_321_: *mut leanh::LeanObject,
    mut v_stop_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_323_ = l_List_toSlice(v_00_u03b1_319_, v_as_320_, v_start_321_, v_stop_322_);
    leanh::lean_dec(v_stop_322_);
    leanh::lean_dec(v_as_320_);
    return v_res_323_;
}
pub unsafe fn l_List_toUnboundedSlice___redArg(
    mut v_as_324_: *mut leanh::LeanObject,
    mut v_start_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_List_drop___redArg(v_start_325_, v_as_324_);
    v___x_327_ = leanh::lean_box(0);
    v___x_328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
    leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
    return v___x_328_;
}
pub unsafe fn l_List_toUnboundedSlice___redArg___boxed(
    mut v_as_329_: *mut leanh::LeanObject,
    mut v_start_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = l_List_toUnboundedSlice___redArg(v_as_329_, v_start_330_);
    leanh::lean_dec(v_as_329_);
    return v_res_331_;
}
pub unsafe fn l_List_toUnboundedSlice(
    mut v_00_u03b1_332_: *mut leanh::LeanObject,
    mut v_as_333_: *mut leanh::LeanObject,
    mut v_start_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = l_List_toUnboundedSlice___redArg(v_as_333_, v_start_334_);
    return v___x_335_;
}
pub unsafe fn l_List_toUnboundedSlice___boxed(
    mut v_00_u03b1_336_: *mut leanh::LeanObject,
    mut v_as_337_: *mut leanh::LeanObject,
    mut v_start_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_List_toUnboundedSlice(v_00_u03b1_336_, v_as_337_, v_start_338_);
    leanh::lean_dec(v_as_337_);
    return v_res_339_;
}
pub unsafe fn l_instSliceableListNatListSlice___lam__0(
    mut v_xs_340_: *mut leanh::LeanObject,
    mut v_range_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_342_ = leanh::lean_ctor_get(v_range_341_, 0);
    leanh::lean_inc(v_lower_342_);
    v_upper_343_ = leanh::lean_ctor_get(v_range_341_, 1);
    leanh::lean_inc(v_upper_343_);
    leanh::lean_dec_ref(v_range_341_);
    v___x_344_ = leanh::lean_unsigned_to_nat(1);
    v___x_345_ = lean_nat_add(v_upper_343_, v___x_344_);
    leanh::lean_dec(v_upper_343_);
    v___x_346_ = l_List_toSlice___redArg(v_xs_340_, v_lower_342_, v___x_345_);
    leanh::lean_dec(v___x_345_);
    return v___x_346_;
}
pub unsafe fn l_instSliceableListNatListSlice___lam__0___boxed(
    mut v_xs_347_: *mut leanh::LeanObject,
    mut v_range_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_instSliceableListNatListSlice___lam__0(v_xs_347_, v_range_348_);
    leanh::lean_dec(v_xs_347_);
    return v_res_349_;
}
pub unsafe fn l_instSliceableListNatListSlice(
    mut v_00_u03b1_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_352_ = l_instSliceableListNatListSlice___closed__0;
    return v___f_352_;
}
pub unsafe fn l_instSliceableListNatListSlice__1___lam__0(
    mut v_xs_353_: *mut leanh::LeanObject,
    mut v_range_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_355_ = leanh::lean_ctor_get(v_range_354_, 0);
    leanh::lean_inc(v_lower_355_);
    v_upper_356_ = leanh::lean_ctor_get(v_range_354_, 1);
    leanh::lean_inc(v_upper_356_);
    leanh::lean_dec_ref(v_range_354_);
    v___x_357_ = l_List_toSlice___redArg(v_xs_353_, v_lower_355_, v_upper_356_);
    leanh::lean_dec(v_upper_356_);
    return v___x_357_;
}
pub unsafe fn l_instSliceableListNatListSlice__1___lam__0___boxed(
    mut v_xs_358_: *mut leanh::LeanObject,
    mut v_range_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_instSliceableListNatListSlice__1___lam__0(v_xs_358_, v_range_359_);
    leanh::lean_dec(v_xs_358_);
    return v_res_360_;
}
pub unsafe fn l_instSliceableListNatListSlice__1(
    mut v_00_u03b1_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_363_ = l_instSliceableListNatListSlice__1___closed__0;
    return v___f_363_;
}
pub unsafe fn l_instSliceableListNatListSlice__2(
    mut v_00_u03b1_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = l_instSliceableListNatListSlice__2___closed__0;
    return v___f_366_;
}
pub unsafe fn l_instSliceableListNatListSlice__3___lam__0(
    mut v_xs_367_: *mut leanh::LeanObject,
    mut v_range_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_369_ = leanh::lean_ctor_get(v_range_368_, 0);
    v_upper_370_ = leanh::lean_ctor_get(v_range_368_, 1);
    v___x_371_ = leanh::lean_unsigned_to_nat(1);
    v___x_372_ = lean_nat_add(v_lower_369_, v___x_371_);
    v___x_373_ = lean_nat_add(v_upper_370_, v___x_371_);
    v___x_374_ = l_List_toSlice___redArg(v_xs_367_, v___x_372_, v___x_373_);
    leanh::lean_dec(v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_instSliceableListNatListSlice__3___lam__0___boxed(
    mut v_xs_375_: *mut leanh::LeanObject,
    mut v_range_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l_instSliceableListNatListSlice__3___lam__0(v_xs_375_, v_range_376_);
    leanh::lean_dec_ref(v_range_376_);
    leanh::lean_dec(v_xs_375_);
    return v_res_377_;
}
pub unsafe fn l_instSliceableListNatListSlice__3(
    mut v_00_u03b1_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_380_ = l_instSliceableListNatListSlice__3___closed__0;
    return v___f_380_;
}
pub unsafe fn l_instSliceableListNatListSlice__4___lam__0(
    mut v_xs_381_: *mut leanh::LeanObject,
    mut v_range_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lower_383_ = leanh::lean_ctor_get(v_range_382_, 0);
    v_upper_384_ = leanh::lean_ctor_get(v_range_382_, 1);
    v___x_385_ = leanh::lean_unsigned_to_nat(1);
    v___x_386_ = lean_nat_add(v_lower_383_, v___x_385_);
    v___x_387_ = l_List_toSlice___redArg(v_xs_381_, v___x_386_, v_upper_384_);
    return v___x_387_;
}
pub unsafe fn l_instSliceableListNatListSlice__4___lam__0___boxed(
    mut v_xs_388_: *mut leanh::LeanObject,
    mut v_range_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_instSliceableListNatListSlice__4___lam__0(v_xs_388_, v_range_389_);
    leanh::lean_dec_ref(v_range_389_);
    leanh::lean_dec(v_xs_388_);
    return v_res_390_;
}
pub unsafe fn l_instSliceableListNatListSlice__4(
    mut v_00_u03b1_392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_393_ = l_instSliceableListNatListSlice__4___closed__0;
    return v___f_393_;
}
pub unsafe fn l_instSliceableListNatListSlice__5___lam__0(
    mut v_xs_394_: *mut leanh::LeanObject,
    mut v_range_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = leanh::lean_unsigned_to_nat(1);
    v___x_397_ = lean_nat_add(v_range_395_, v___x_396_);
    v___x_398_ = l_List_toUnboundedSlice___redArg(v_xs_394_, v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_instSliceableListNatListSlice__5___lam__0___boxed(
    mut v_xs_399_: *mut leanh::LeanObject,
    mut v_range_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ = l_instSliceableListNatListSlice__5___lam__0(v_xs_399_, v_range_400_);
    leanh::lean_dec(v_range_400_);
    leanh::lean_dec(v_xs_399_);
    return v_res_401_;
}
pub unsafe fn l_instSliceableListNatListSlice__5(
    mut v_00_u03b1_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_404_ = l_instSliceableListNatListSlice__5___closed__0;
    return v___f_404_;
}
pub unsafe fn l_instSliceableListNatListSlice__6___lam__0(
    mut v_xs_405_: *mut leanh::LeanObject,
    mut v_range_406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = leanh::lean_unsigned_to_nat(0);
    v___x_408_ = leanh::lean_unsigned_to_nat(1);
    v___x_409_ = lean_nat_add(v_range_406_, v___x_408_);
    v___x_410_ = l_List_toSlice___redArg(v_xs_405_, v___x_407_, v___x_409_);
    leanh::lean_dec(v___x_409_);
    return v___x_410_;
}
pub unsafe fn l_instSliceableListNatListSlice__6___lam__0___boxed(
    mut v_xs_411_: *mut leanh::LeanObject,
    mut v_range_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ = l_instSliceableListNatListSlice__6___lam__0(v_xs_411_, v_range_412_);
    leanh::lean_dec(v_range_412_);
    leanh::lean_dec(v_xs_411_);
    return v_res_413_;
}
pub unsafe fn l_instSliceableListNatListSlice__6(
    mut v_00_u03b1_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_416_ = l_instSliceableListNatListSlice__6___closed__0;
    return v___f_416_;
}
pub unsafe fn l_instSliceableListNatListSlice__7___lam__0(
    mut v_xs_417_: *mut leanh::LeanObject,
    mut v_range_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = leanh::lean_unsigned_to_nat(0);
    v___x_420_ = l_List_toSlice___redArg(v_xs_417_, v___x_419_, v_range_418_);
    return v___x_420_;
}
pub unsafe fn l_instSliceableListNatListSlice__7___lam__0___boxed(
    mut v_xs_421_: *mut leanh::LeanObject,
    mut v_range_422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_instSliceableListNatListSlice__7___lam__0(v_xs_421_, v_range_422_);
    leanh::lean_dec(v_range_422_);
    leanh::lean_dec(v_xs_421_);
    return v_res_423_;
}
pub unsafe fn l_instSliceableListNatListSlice__7(
    mut v_00_u03b1_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_426_ = l_instSliceableListNatListSlice__7___closed__0;
    return v___f_426_;
}
pub unsafe fn l_instSliceableListNatListSlice__8___lam__0(
    mut v_xs_427_: *mut leanh::LeanObject,
    mut v_x_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = leanh::lean_unsigned_to_nat(0);
    v___x_430_ = l_List_toUnboundedSlice___redArg(v_xs_427_, v___x_429_);
    return v___x_430_;
}
pub unsafe fn l_instSliceableListNatListSlice__8___lam__0___boxed(
    mut v_xs_431_: *mut leanh::LeanObject,
    mut v_x_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_instSliceableListNatListSlice__8___lam__0(v_xs_431_, v_x_432_);
    leanh::lean_dec(v_xs_431_);
    return v_res_433_;
}
pub unsafe fn l_instSliceableListNatListSlice__8(
    mut v_00_u03b1_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_436_ = l_instSliceableListNatListSlice__8___closed__0;
    return v___f_436_;
}
pub unsafe fn l_instSliceableListSliceNat___lam__0(
    mut v_xs_437_: *mut leanh::LeanObject,
    mut v_range_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_439_ = leanh::lean_ctor_get(v_xs_437_, 0);
                leanh::lean_inc(v_list_439_);
                v_stop_440_ = leanh::lean_ctor_get(v_xs_437_, 1);
                leanh::lean_inc(v_stop_440_);
                leanh::lean_dec_ref(v_xs_437_);
                if leanh::lean_obj_tag(v_stop_440_) == 0 {
                    v_upper_445_ = leanh::lean_ctor_get(v_range_438_, 1);
                    v___x_446_ = leanh::lean_unsigned_to_nat(1);
                    v___x_447_ = lean_nat_add(v_upper_445_, v___x_446_);
                    v___y_442_ = v___x_447_;
                    state = 1;
                    continue;
                } else {
                    v_val_448_ = leanh::lean_ctor_get(v_stop_440_, 0);
                    leanh::lean_inc(v_val_448_);
                    leanh::lean_dec_ref_known(v_stop_440_, 1);
                    v_upper_449_ = leanh::lean_ctor_get(v_range_438_, 1);
                    v___x_450_ = leanh::lean_unsigned_to_nat(1);
                    v___x_451_ = lean_nat_add(v_upper_449_, v___x_450_);
                    v___x_452_ = lean_nat_dec_le(v_val_448_, v___x_451_);
                    if v___x_452_ == 0 {
                        leanh::lean_dec(v_val_448_);
                        v___y_442_ = v___x_451_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_451_);
                        v___y_442_ = v_val_448_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_443_ = leanh::lean_ctor_get(v_range_438_, 0);
                leanh::lean_inc(v_lower_443_);
                leanh::lean_dec_ref(v_range_438_);
                v___x_444_ = l_List_toSlice___redArg(v_list_439_, v_lower_443_, v___y_442_);
                leanh::lean_dec(v___y_442_);
                leanh::lean_dec(v_list_439_);
                return v___x_444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat(
    mut v_00_u03b1_454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_455_ = l_instSliceableListSliceNat___closed__0;
    return v___f_455_;
}
pub unsafe fn l_instSliceableListSliceNat__1___lam__0(
    mut v_xs_456_: *mut leanh::LeanObject,
    mut v_range_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_458_ = leanh::lean_ctor_get(v_xs_456_, 0);
                leanh::lean_inc(v_list_458_);
                v_stop_459_ = leanh::lean_ctor_get(v_xs_456_, 1);
                leanh::lean_inc(v_stop_459_);
                leanh::lean_dec_ref(v_xs_456_);
                if leanh::lean_obj_tag(v_stop_459_) == 0 {
                    v_upper_464_ = leanh::lean_ctor_get(v_range_457_, 1);
                    leanh::lean_inc(v_upper_464_);
                    v___y_461_ = v_upper_464_;
                    state = 1;
                    continue;
                } else {
                    v_val_465_ = leanh::lean_ctor_get(v_stop_459_, 0);
                    leanh::lean_inc(v_val_465_);
                    leanh::lean_dec_ref_known(v_stop_459_, 1);
                    v_upper_466_ = leanh::lean_ctor_get(v_range_457_, 1);
                    v___x_467_ = lean_nat_dec_le(v_val_465_, v_upper_466_);
                    if v___x_467_ == 0 {
                        leanh::lean_dec(v_val_465_);
                        leanh::lean_inc(v_upper_466_);
                        v___y_461_ = v_upper_466_;
                        state = 1;
                        continue;
                    } else {
                        v___y_461_ = v_val_465_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_462_ = leanh::lean_ctor_get(v_range_457_, 0);
                leanh::lean_inc(v_lower_462_);
                leanh::lean_dec_ref(v_range_457_);
                v___x_463_ = l_List_toSlice___redArg(v_list_458_, v_lower_462_, v___y_461_);
                leanh::lean_dec(v___y_461_);
                leanh::lean_dec(v_list_458_);
                return v___x_463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__1(
    mut v_00_u03b1_469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_470_ = l_instSliceableListSliceNat__1___closed__0;
    return v___f_470_;
}
pub unsafe fn l_instSliceableListSliceNat__2___lam__0(
    mut v_xs_471_: *mut leanh::LeanObject,
    mut v_range_472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stop_473_ = leanh::lean_ctor_get(v_xs_471_, 1);
    if leanh::lean_obj_tag(v_stop_473_) == 0 {
        let mut v_list_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_list_474_ = leanh::lean_ctor_get(v_xs_471_, 0);
        v___x_475_ = l_List_toUnboundedSlice___redArg(v_list_474_, v_range_472_);
        return v___x_475_;
    } else {
        let mut v_list_476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_list_476_ = leanh::lean_ctor_get(v_xs_471_, 0);
        v_val_477_ = leanh::lean_ctor_get(v_stop_473_, 0);
        v___x_478_ = l_List_toSlice___redArg(v_list_476_, v_range_472_, v_val_477_);
        return v___x_478_;
    }
}
pub unsafe fn l_instSliceableListSliceNat__2___lam__0___boxed(
    mut v_xs_479_: *mut leanh::LeanObject,
    mut v_range_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_481_ = l_instSliceableListSliceNat__2___lam__0(v_xs_479_, v_range_480_);
    leanh::lean_dec_ref(v_xs_479_);
    return v_res_481_;
}
pub unsafe fn l_instSliceableListSliceNat__2(
    mut v_00_u03b1_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_484_ = l_instSliceableListSliceNat__2___closed__0;
    return v___f_484_;
}
pub unsafe fn l_instSliceableListSliceNat__3___lam__0(
    mut v_xs_485_: *mut leanh::LeanObject,
    mut v_range_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_487_ = leanh::lean_ctor_get(v_xs_485_, 0);
                leanh::lean_inc(v_list_487_);
                v_stop_488_ = leanh::lean_ctor_get(v_xs_485_, 1);
                leanh::lean_inc(v_stop_488_);
                leanh::lean_dec_ref(v_xs_485_);
                if leanh::lean_obj_tag(v_stop_488_) == 0 {
                    v_upper_495_ = leanh::lean_ctor_get(v_range_486_, 1);
                    v___x_496_ = leanh::lean_unsigned_to_nat(1);
                    v___x_497_ = lean_nat_add(v_upper_495_, v___x_496_);
                    v___y_490_ = v___x_497_;
                    state = 1;
                    continue;
                } else {
                    v_val_498_ = leanh::lean_ctor_get(v_stop_488_, 0);
                    leanh::lean_inc(v_val_498_);
                    leanh::lean_dec_ref_known(v_stop_488_, 1);
                    v_upper_499_ = leanh::lean_ctor_get(v_range_486_, 1);
                    v___x_500_ = leanh::lean_unsigned_to_nat(1);
                    v___x_501_ = lean_nat_add(v_upper_499_, v___x_500_);
                    v___x_502_ = lean_nat_dec_le(v_val_498_, v___x_501_);
                    if v___x_502_ == 0 {
                        leanh::lean_dec(v_val_498_);
                        v___y_490_ = v___x_501_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_501_);
                        v___y_490_ = v_val_498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_491_ = leanh::lean_ctor_get(v_range_486_, 0);
                v___x_492_ = leanh::lean_unsigned_to_nat(1);
                v___x_493_ = lean_nat_add(v_lower_491_, v___x_492_);
                v___x_494_ = l_List_toSlice___redArg(v_list_487_, v___x_493_, v___y_490_);
                leanh::lean_dec(v___y_490_);
                leanh::lean_dec(v_list_487_);
                return v___x_494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__3___lam__0___boxed(
    mut v_xs_503_: *mut leanh::LeanObject,
    mut v_range_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_505_ = l_instSliceableListSliceNat__3___lam__0(v_xs_503_, v_range_504_);
    leanh::lean_dec_ref(v_range_504_);
    return v_res_505_;
}
pub unsafe fn l_instSliceableListSliceNat__3(
    mut v_00_u03b1_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_508_ = l_instSliceableListSliceNat__3___closed__0;
    return v___f_508_;
}
pub unsafe fn l_instSliceableListSliceNat__4___lam__0(
    mut v_xs_509_: *mut leanh::LeanObject,
    mut v_range_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_511_ = leanh::lean_ctor_get(v_xs_509_, 0);
                v_stop_512_ = leanh::lean_ctor_get(v_xs_509_, 1);
                if leanh::lean_obj_tag(v_stop_512_) == 0 {
                    v_upper_519_ = leanh::lean_ctor_get(v_range_510_, 1);
                    v___y_514_ = v_upper_519_;
                    state = 1;
                    continue;
                } else {
                    v_val_520_ = leanh::lean_ctor_get(v_stop_512_, 0);
                    v_upper_521_ = leanh::lean_ctor_get(v_range_510_, 1);
                    v___x_522_ = lean_nat_dec_le(v_val_520_, v_upper_521_);
                    if v___x_522_ == 0 {
                        v___y_514_ = v_upper_521_;
                        state = 1;
                        continue;
                    } else {
                        v___y_514_ = v_val_520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_515_ = leanh::lean_ctor_get(v_range_510_, 0);
                v___x_516_ = leanh::lean_unsigned_to_nat(1);
                v___x_517_ = lean_nat_add(v_lower_515_, v___x_516_);
                v___x_518_ = l_List_toSlice___redArg(v_list_511_, v___x_517_, v___y_514_);
                return v___x_518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__4___lam__0___boxed(
    mut v_xs_523_: *mut leanh::LeanObject,
    mut v_range_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_525_ = l_instSliceableListSliceNat__4___lam__0(v_xs_523_, v_range_524_);
    leanh::lean_dec_ref(v_range_524_);
    leanh::lean_dec_ref(v_xs_523_);
    return v_res_525_;
}
pub unsafe fn l_instSliceableListSliceNat__4(
    mut v_00_u03b1_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_528_ = l_instSliceableListSliceNat__4___closed__0;
    return v___f_528_;
}
pub unsafe fn l_instSliceableListSliceNat__5___lam__0(
    mut v_xs_529_: *mut leanh::LeanObject,
    mut v_range_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_stop_531_ = leanh::lean_ctor_get(v_xs_529_, 1);
    if leanh::lean_obj_tag(v_stop_531_) == 0 {
        let mut v_list_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_list_532_ = leanh::lean_ctor_get(v_xs_529_, 0);
        v___x_533_ = leanh::lean_unsigned_to_nat(1);
        v___x_534_ = lean_nat_add(v_range_530_, v___x_533_);
        v___x_535_ = l_List_toUnboundedSlice___redArg(v_list_532_, v___x_534_);
        return v___x_535_;
    } else {
        let mut v_list_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_list_536_ = leanh::lean_ctor_get(v_xs_529_, 0);
        v_val_537_ = leanh::lean_ctor_get(v_stop_531_, 0);
        v___x_538_ = leanh::lean_unsigned_to_nat(1);
        v___x_539_ = lean_nat_add(v_range_530_, v___x_538_);
        v___x_540_ = l_List_toSlice___redArg(v_list_536_, v___x_539_, v_val_537_);
        return v___x_540_;
    }
}
pub unsafe fn l_instSliceableListSliceNat__5___lam__0___boxed(
    mut v_xs_541_: *mut leanh::LeanObject,
    mut v_range_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_instSliceableListSliceNat__5___lam__0(v_xs_541_, v_range_542_);
    leanh::lean_dec(v_range_542_);
    leanh::lean_dec_ref(v_xs_541_);
    return v_res_543_;
}
pub unsafe fn l_instSliceableListSliceNat__5(
    mut v_00_u03b1_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_546_ = l_instSliceableListSliceNat__5___closed__0;
    return v___f_546_;
}
pub unsafe fn l_instSliceableListSliceNat__6___lam__0(
    mut v_xs_547_: *mut leanh::LeanObject,
    mut v_range_548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_549_ = leanh::lean_ctor_get(v_xs_547_, 0);
                leanh::lean_inc(v_list_549_);
                v_stop_550_ = leanh::lean_ctor_get(v_xs_547_, 1);
                leanh::lean_inc(v_stop_550_);
                leanh::lean_dec_ref(v_xs_547_);
                if leanh::lean_obj_tag(v_stop_550_) == 0 {
                    v___x_555_ = leanh::lean_unsigned_to_nat(1);
                    v___x_556_ = lean_nat_add(v_range_548_, v___x_555_);
                    v___y_552_ = v___x_556_;
                    state = 1;
                    continue;
                } else {
                    v_val_557_ = leanh::lean_ctor_get(v_stop_550_, 0);
                    leanh::lean_inc(v_val_557_);
                    leanh::lean_dec_ref_known(v_stop_550_, 1);
                    v___x_558_ = leanh::lean_unsigned_to_nat(1);
                    v___x_559_ = lean_nat_add(v_range_548_, v___x_558_);
                    v___x_560_ = lean_nat_dec_le(v_val_557_, v___x_559_);
                    if v___x_560_ == 0 {
                        leanh::lean_dec(v_val_557_);
                        v___y_552_ = v___x_559_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_559_);
                        v___y_552_ = v_val_557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_553_ = leanh::lean_unsigned_to_nat(0);
                v___x_554_ = l_List_toSlice___redArg(v_list_549_, v___x_553_, v___y_552_);
                leanh::lean_dec(v___y_552_);
                leanh::lean_dec(v_list_549_);
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__6___lam__0___boxed(
    mut v_xs_561_: *mut leanh::LeanObject,
    mut v_range_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_instSliceableListSliceNat__6___lam__0(v_xs_561_, v_range_562_);
    leanh::lean_dec(v_range_562_);
    return v_res_563_;
}
pub unsafe fn l_instSliceableListSliceNat__6(
    mut v_00_u03b1_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_566_ = l_instSliceableListSliceNat__6___closed__0;
    return v___f_566_;
}
pub unsafe fn l_instSliceableListSliceNat__7___lam__0(
    mut v_xs_567_: *mut leanh::LeanObject,
    mut v_range_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_list_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_569_ = leanh::lean_ctor_get(v_xs_567_, 0);
                v_stop_570_ = leanh::lean_ctor_get(v_xs_567_, 1);
                if leanh::lean_obj_tag(v_stop_570_) == 0 {
                    v___y_572_ = v_range_568_;
                    state = 1;
                    continue;
                } else {
                    v_val_575_ = leanh::lean_ctor_get(v_stop_570_, 0);
                    v___x_576_ = lean_nat_dec_le(v_val_575_, v_range_568_);
                    if v___x_576_ == 0 {
                        v___y_572_ = v_range_568_;
                        state = 1;
                        continue;
                    } else {
                        v___y_572_ = v_val_575_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_573_ = leanh::lean_unsigned_to_nat(0);
                v___x_574_ = l_List_toSlice___redArg(v_list_569_, v___x_573_, v___y_572_);
                return v___x_574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__7___lam__0___boxed(
    mut v_xs_577_: *mut leanh::LeanObject,
    mut v_range_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_instSliceableListSliceNat__7___lam__0(v_xs_577_, v_range_578_);
    leanh::lean_dec(v_range_578_);
    leanh::lean_dec_ref(v_xs_577_);
    return v_res_579_;
}
pub unsafe fn l_instSliceableListSliceNat__7(
    mut v_00_u03b1_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_582_ = l_instSliceableListSliceNat__7___closed__0;
    return v___f_582_;
}
pub unsafe fn l_instSliceableListSliceNat__8___lam__0(
    mut v_xs_583_: *mut leanh::LeanObject,
    mut v_x_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_583_);
    return v_xs_583_;
}
pub unsafe fn l_instSliceableListSliceNat__8___lam__0___boxed(
    mut v_xs_585_: *mut leanh::LeanObject,
    mut v_x_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ = l_instSliceableListSliceNat__8___lam__0(v_xs_585_, v_x_586_);
    leanh::lean_dec_ref(v_xs_585_);
    return v_res_587_;
}
pub unsafe fn l_instSliceableListSliceNat__8(
    mut v_00_u03b1_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_590_ = l_instSliceableListSliceNat__8___closed__0;
    return v___f_590_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Basic(
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
pub unsafe fn initialize_Init_Data_Slice_List_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Basic(builtin);
}