// Lean compiler output
// Module: Init.Data.Slice.List.Basic
// Imports: Init.Data.Slice.Basic Init.Data.Slice.Notation
use crate::r#gen::Init::Data::List::Basic::l_List_drop___redArg;
use crate::r#gen::Init::Data::Slice::Basic::{
    initialize_Init_Data_Slice_Basic, runtime_initialize_Init_Data_Slice_Basic,
};
use crate::r#gen::Init::Data::Slice::Notation::{
    initialize_Init_Data_Slice_Notation, runtime_initialize_Init_Data_Slice_Notation,
};
use crate::ffi::{
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
pub static l_List_toSlice___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_List_toSlice___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_toSlice___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_toSlice___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_toSlice___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_toSlice___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_toSlice___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListNatListSlice___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListNatListSlice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__1___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__2___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_List_toUnboundedSlice___redArg___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__3___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__3___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__4___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__4___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__5___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__5___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__6___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__6___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__7___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__7___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__7___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__7___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListNatListSlice__8___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSliceableListNatListSlice__8___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSliceableListNatListSlice__8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListNatListSlice__8___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__1___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__2___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__2___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__3___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__3___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__4___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__4___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__5___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__5___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__6___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__6___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__7___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__7___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__7___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__7___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instSliceableListSliceNat__8___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSliceableListSliceNat__8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSliceableListSliceNat__8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSliceableListSliceNat__8___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_List_toSlice___redArg(
    mut v_as_301_: *mut crate::leanh::LeanObject,
    mut v_start_302_: *mut crate::leanh::LeanObject,
    mut v_stop_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_304_: u8 = 0;
    v___x_304_ = lean_nat_dec_lt(v_start_302_, v_stop_303_);
    if v___x_304_ == 0 {
        let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_start_302_);
        v___x_305_ = l_List_toSlice___redArg___closed__1;
        return v___x_305_;
    } else {
        let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_start_302_);
        v___x_306_ = l_List_drop___redArg(v_start_302_, v_as_301_);
        v___x_307_ = lean_nat_sub(v_stop_303_, v_start_302_);
        crate::leanh::lean_dec(v_start_302_);
        v___x_308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_308_, 0, v___x_307_);
        v___x_309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_309_, 0, v___x_306_);
        crate::leanh::lean_ctor_set(v___x_309_, 1, v___x_308_);
        return v___x_309_;
    }
}
pub unsafe fn l_List_toSlice___redArg___boxed(
    mut v_as_310_: *mut crate::leanh::LeanObject,
    mut v_start_311_: *mut crate::leanh::LeanObject,
    mut v_stop_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_List_toSlice___redArg(v_as_310_, v_start_311_, v_stop_312_);
    crate::leanh::lean_dec(v_stop_312_);
    crate::leanh::lean_dec(v_as_310_);
    return v_res_313_;
}
pub unsafe fn l_List_toSlice(
    mut v_00_u03b1_314_: *mut crate::leanh::LeanObject,
    mut v_as_315_: *mut crate::leanh::LeanObject,
    mut v_start_316_: *mut crate::leanh::LeanObject,
    mut v_stop_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_318_ = l_List_toSlice___redArg(v_as_315_, v_start_316_, v_stop_317_);
    return v___x_318_;
}
pub unsafe fn l_List_toSlice___boxed(
    mut v_00_u03b1_319_: *mut crate::leanh::LeanObject,
    mut v_as_320_: *mut crate::leanh::LeanObject,
    mut v_start_321_: *mut crate::leanh::LeanObject,
    mut v_stop_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_323_ = l_List_toSlice(v_00_u03b1_319_, v_as_320_, v_start_321_, v_stop_322_);
    crate::leanh::lean_dec(v_stop_322_);
    crate::leanh::lean_dec(v_as_320_);
    return v_res_323_;
}
pub unsafe fn l_List_toUnboundedSlice___redArg(
    mut v_as_324_: *mut crate::leanh::LeanObject,
    mut v_start_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_List_drop___redArg(v_start_325_, v_as_324_);
    v___x_327_ = crate::leanh::lean_box(0);
    v___x_328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_328_, 0, v___x_326_);
    crate::leanh::lean_ctor_set(v___x_328_, 1, v___x_327_);
    return v___x_328_;
}
pub unsafe fn l_List_toUnboundedSlice___redArg___boxed(
    mut v_as_329_: *mut crate::leanh::LeanObject,
    mut v_start_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = l_List_toUnboundedSlice___redArg(v_as_329_, v_start_330_);
    crate::leanh::lean_dec(v_as_329_);
    return v_res_331_;
}
pub unsafe fn l_List_toUnboundedSlice(
    mut v_00_u03b1_332_: *mut crate::leanh::LeanObject,
    mut v_as_333_: *mut crate::leanh::LeanObject,
    mut v_start_334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_335_ = l_List_toUnboundedSlice___redArg(v_as_333_, v_start_334_);
    return v___x_335_;
}
pub unsafe fn l_List_toUnboundedSlice___boxed(
    mut v_00_u03b1_336_: *mut crate::leanh::LeanObject,
    mut v_as_337_: *mut crate::leanh::LeanObject,
    mut v_start_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_339_ = l_List_toUnboundedSlice(v_00_u03b1_336_, v_as_337_, v_start_338_);
    crate::leanh::lean_dec(v_as_337_);
    return v_res_339_;
}
pub unsafe fn l_instSliceableListNatListSlice___lam__0(
    mut v_xs_340_: *mut crate::leanh::LeanObject,
    mut v_range_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_342_ = crate::leanh::lean_ctor_get(v_range_341_, 0);
    crate::leanh::lean_inc(v_lower_342_);
    v_upper_343_ = crate::leanh::lean_ctor_get(v_range_341_, 1);
    crate::leanh::lean_inc(v_upper_343_);
    crate::leanh::lean_dec_ref(v_range_341_);
    v___x_344_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_345_ = lean_nat_add(v_upper_343_, v___x_344_);
    crate::leanh::lean_dec(v_upper_343_);
    v___x_346_ = l_List_toSlice___redArg(v_xs_340_, v_lower_342_, v___x_345_);
    crate::leanh::lean_dec(v___x_345_);
    return v___x_346_;
}
pub unsafe fn l_instSliceableListNatListSlice___lam__0___boxed(
    mut v_xs_347_: *mut crate::leanh::LeanObject,
    mut v_range_348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_349_ = l_instSliceableListNatListSlice___lam__0(v_xs_347_, v_range_348_);
    crate::leanh::lean_dec(v_xs_347_);
    return v_res_349_;
}
pub unsafe fn l_instSliceableListNatListSlice(
    mut v_00_u03b1_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_352_ = l_instSliceableListNatListSlice___closed__0;
    return v___f_352_;
}
pub unsafe fn l_instSliceableListNatListSlice__1___lam__0(
    mut v_xs_353_: *mut crate::leanh::LeanObject,
    mut v_range_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_355_ = crate::leanh::lean_ctor_get(v_range_354_, 0);
    crate::leanh::lean_inc(v_lower_355_);
    v_upper_356_ = crate::leanh::lean_ctor_get(v_range_354_, 1);
    crate::leanh::lean_inc(v_upper_356_);
    crate::leanh::lean_dec_ref(v_range_354_);
    v___x_357_ = l_List_toSlice___redArg(v_xs_353_, v_lower_355_, v_upper_356_);
    crate::leanh::lean_dec(v_upper_356_);
    return v___x_357_;
}
pub unsafe fn l_instSliceableListNatListSlice__1___lam__0___boxed(
    mut v_xs_358_: *mut crate::leanh::LeanObject,
    mut v_range_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_instSliceableListNatListSlice__1___lam__0(v_xs_358_, v_range_359_);
    crate::leanh::lean_dec(v_xs_358_);
    return v_res_360_;
}
pub unsafe fn l_instSliceableListNatListSlice__1(
    mut v_00_u03b1_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_363_ = l_instSliceableListNatListSlice__1___closed__0;
    return v___f_363_;
}
pub unsafe fn l_instSliceableListNatListSlice__2(
    mut v_00_u03b1_365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_366_ = l_instSliceableListNatListSlice__2___closed__0;
    return v___f_366_;
}
pub unsafe fn l_instSliceableListNatListSlice__3___lam__0(
    mut v_xs_367_: *mut crate::leanh::LeanObject,
    mut v_range_368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_369_ = crate::leanh::lean_ctor_get(v_range_368_, 0);
    v_upper_370_ = crate::leanh::lean_ctor_get(v_range_368_, 1);
    v___x_371_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_372_ = lean_nat_add(v_lower_369_, v___x_371_);
    v___x_373_ = lean_nat_add(v_upper_370_, v___x_371_);
    v___x_374_ = l_List_toSlice___redArg(v_xs_367_, v___x_372_, v___x_373_);
    crate::leanh::lean_dec(v___x_373_);
    return v___x_374_;
}
pub unsafe fn l_instSliceableListNatListSlice__3___lam__0___boxed(
    mut v_xs_375_: *mut crate::leanh::LeanObject,
    mut v_range_376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_377_ = l_instSliceableListNatListSlice__3___lam__0(v_xs_375_, v_range_376_);
    crate::leanh::lean_dec_ref(v_range_376_);
    crate::leanh::lean_dec(v_xs_375_);
    return v_res_377_;
}
pub unsafe fn l_instSliceableListNatListSlice__3(
    mut v_00_u03b1_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_380_ = l_instSliceableListNatListSlice__3___closed__0;
    return v___f_380_;
}
pub unsafe fn l_instSliceableListNatListSlice__4___lam__0(
    mut v_xs_381_: *mut crate::leanh::LeanObject,
    mut v_range_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lower_383_ = crate::leanh::lean_ctor_get(v_range_382_, 0);
    v_upper_384_ = crate::leanh::lean_ctor_get(v_range_382_, 1);
    v___x_385_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_386_ = lean_nat_add(v_lower_383_, v___x_385_);
    v___x_387_ = l_List_toSlice___redArg(v_xs_381_, v___x_386_, v_upper_384_);
    return v___x_387_;
}
pub unsafe fn l_instSliceableListNatListSlice__4___lam__0___boxed(
    mut v_xs_388_: *mut crate::leanh::LeanObject,
    mut v_range_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_instSliceableListNatListSlice__4___lam__0(v_xs_388_, v_range_389_);
    crate::leanh::lean_dec_ref(v_range_389_);
    crate::leanh::lean_dec(v_xs_388_);
    return v_res_390_;
}
pub unsafe fn l_instSliceableListNatListSlice__4(
    mut v_00_u03b1_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_393_ = l_instSliceableListNatListSlice__4___closed__0;
    return v___f_393_;
}
pub unsafe fn l_instSliceableListNatListSlice__5___lam__0(
    mut v_xs_394_: *mut crate::leanh::LeanObject,
    mut v_range_395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_396_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_397_ = lean_nat_add(v_range_395_, v___x_396_);
    v___x_398_ = l_List_toUnboundedSlice___redArg(v_xs_394_, v___x_397_);
    return v___x_398_;
}
pub unsafe fn l_instSliceableListNatListSlice__5___lam__0___boxed(
    mut v_xs_399_: *mut crate::leanh::LeanObject,
    mut v_range_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ = l_instSliceableListNatListSlice__5___lam__0(v_xs_399_, v_range_400_);
    crate::leanh::lean_dec(v_range_400_);
    crate::leanh::lean_dec(v_xs_399_);
    return v_res_401_;
}
pub unsafe fn l_instSliceableListNatListSlice__5(
    mut v_00_u03b1_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_404_ = l_instSliceableListNatListSlice__5___closed__0;
    return v___f_404_;
}
pub unsafe fn l_instSliceableListNatListSlice__6___lam__0(
    mut v_xs_405_: *mut crate::leanh::LeanObject,
    mut v_range_406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_407_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_408_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_409_ = lean_nat_add(v_range_406_, v___x_408_);
    v___x_410_ = l_List_toSlice___redArg(v_xs_405_, v___x_407_, v___x_409_);
    crate::leanh::lean_dec(v___x_409_);
    return v___x_410_;
}
pub unsafe fn l_instSliceableListNatListSlice__6___lam__0___boxed(
    mut v_xs_411_: *mut crate::leanh::LeanObject,
    mut v_range_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ = l_instSliceableListNatListSlice__6___lam__0(v_xs_411_, v_range_412_);
    crate::leanh::lean_dec(v_range_412_);
    crate::leanh::lean_dec(v_xs_411_);
    return v_res_413_;
}
pub unsafe fn l_instSliceableListNatListSlice__6(
    mut v_00_u03b1_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_416_ = l_instSliceableListNatListSlice__6___closed__0;
    return v___f_416_;
}
pub unsafe fn l_instSliceableListNatListSlice__7___lam__0(
    mut v_xs_417_: *mut crate::leanh::LeanObject,
    mut v_range_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_419_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_420_ = l_List_toSlice___redArg(v_xs_417_, v___x_419_, v_range_418_);
    return v___x_420_;
}
pub unsafe fn l_instSliceableListNatListSlice__7___lam__0___boxed(
    mut v_xs_421_: *mut crate::leanh::LeanObject,
    mut v_range_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_423_ = l_instSliceableListNatListSlice__7___lam__0(v_xs_421_, v_range_422_);
    crate::leanh::lean_dec(v_range_422_);
    crate::leanh::lean_dec(v_xs_421_);
    return v_res_423_;
}
pub unsafe fn l_instSliceableListNatListSlice__7(
    mut v_00_u03b1_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_426_ = l_instSliceableListNatListSlice__7___closed__0;
    return v___f_426_;
}
pub unsafe fn l_instSliceableListNatListSlice__8___lam__0(
    mut v_xs_427_: *mut crate::leanh::LeanObject,
    mut v_x_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_429_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_430_ = l_List_toUnboundedSlice___redArg(v_xs_427_, v___x_429_);
    return v___x_430_;
}
pub unsafe fn l_instSliceableListNatListSlice__8___lam__0___boxed(
    mut v_xs_431_: *mut crate::leanh::LeanObject,
    mut v_x_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_instSliceableListNatListSlice__8___lam__0(v_xs_431_, v_x_432_);
    crate::leanh::lean_dec(v_xs_431_);
    return v_res_433_;
}
pub unsafe fn l_instSliceableListNatListSlice__8(
    mut v_00_u03b1_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_436_ = l_instSliceableListNatListSlice__8___closed__0;
    return v___f_436_;
}
pub unsafe fn l_instSliceableListSliceNat___lam__0(
    mut v_xs_437_: *mut crate::leanh::LeanObject,
    mut v_range_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_439_ = crate::leanh::lean_ctor_get(v_xs_437_, 0);
                crate::leanh::lean_inc(v_list_439_);
                v_stop_440_ = crate::leanh::lean_ctor_get(v_xs_437_, 1);
                crate::leanh::lean_inc(v_stop_440_);
                crate::leanh::lean_dec_ref(v_xs_437_);
                if crate::leanh::lean_obj_tag(v_stop_440_) == 0 {
                    v_upper_445_ = crate::leanh::lean_ctor_get(v_range_438_, 1);
                    v___x_446_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_447_ = lean_nat_add(v_upper_445_, v___x_446_);
                    v___y_442_ = v___x_447_;
                    state = 1;
                    continue;
                } else {
                    v_val_448_ = crate::leanh::lean_ctor_get(v_stop_440_, 0);
                    crate::leanh::lean_inc(v_val_448_);
                    crate::leanh::lean_dec_ref_known(v_stop_440_, 1);
                    v_upper_449_ = crate::leanh::lean_ctor_get(v_range_438_, 1);
                    v___x_450_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_451_ = lean_nat_add(v_upper_449_, v___x_450_);
                    v___x_452_ = lean_nat_dec_le(v_val_448_, v___x_451_);
                    if v___x_452_ == 0 {
                        crate::leanh::lean_dec(v_val_448_);
                        v___y_442_ = v___x_451_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_451_);
                        v___y_442_ = v_val_448_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_443_ = crate::leanh::lean_ctor_get(v_range_438_, 0);
                crate::leanh::lean_inc(v_lower_443_);
                crate::leanh::lean_dec_ref(v_range_438_);
                v___x_444_ = l_List_toSlice___redArg(v_list_439_, v_lower_443_, v___y_442_);
                crate::leanh::lean_dec(v___y_442_);
                crate::leanh::lean_dec(v_list_439_);
                return v___x_444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat(
    mut v_00_u03b1_454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_455_ = l_instSliceableListSliceNat___closed__0;
    return v___f_455_;
}
pub unsafe fn l_instSliceableListSliceNat__1___lam__0(
    mut v_xs_456_: *mut crate::leanh::LeanObject,
    mut v_range_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_458_ = crate::leanh::lean_ctor_get(v_xs_456_, 0);
                crate::leanh::lean_inc(v_list_458_);
                v_stop_459_ = crate::leanh::lean_ctor_get(v_xs_456_, 1);
                crate::leanh::lean_inc(v_stop_459_);
                crate::leanh::lean_dec_ref(v_xs_456_);
                if crate::leanh::lean_obj_tag(v_stop_459_) == 0 {
                    v_upper_464_ = crate::leanh::lean_ctor_get(v_range_457_, 1);
                    crate::leanh::lean_inc(v_upper_464_);
                    v___y_461_ = v_upper_464_;
                    state = 1;
                    continue;
                } else {
                    v_val_465_ = crate::leanh::lean_ctor_get(v_stop_459_, 0);
                    crate::leanh::lean_inc(v_val_465_);
                    crate::leanh::lean_dec_ref_known(v_stop_459_, 1);
                    v_upper_466_ = crate::leanh::lean_ctor_get(v_range_457_, 1);
                    v___x_467_ = lean_nat_dec_le(v_val_465_, v_upper_466_);
                    if v___x_467_ == 0 {
                        crate::leanh::lean_dec(v_val_465_);
                        crate::leanh::lean_inc(v_upper_466_);
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
                v_lower_462_ = crate::leanh::lean_ctor_get(v_range_457_, 0);
                crate::leanh::lean_inc(v_lower_462_);
                crate::leanh::lean_dec_ref(v_range_457_);
                v___x_463_ = l_List_toSlice___redArg(v_list_458_, v_lower_462_, v___y_461_);
                crate::leanh::lean_dec(v___y_461_);
                crate::leanh::lean_dec(v_list_458_);
                return v___x_463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__1(
    mut v_00_u03b1_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_470_ = l_instSliceableListSliceNat__1___closed__0;
    return v___f_470_;
}
pub unsafe fn l_instSliceableListSliceNat__2___lam__0(
    mut v_xs_471_: *mut crate::leanh::LeanObject,
    mut v_range_472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stop_473_ = crate::leanh::lean_ctor_get(v_xs_471_, 1);
    if crate::leanh::lean_obj_tag(v_stop_473_) == 0 {
        let mut v_list_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_list_474_ = crate::leanh::lean_ctor_get(v_xs_471_, 0);
        v___x_475_ = l_List_toUnboundedSlice___redArg(v_list_474_, v_range_472_);
        return v___x_475_;
    } else {
        let mut v_list_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_list_476_ = crate::leanh::lean_ctor_get(v_xs_471_, 0);
        v_val_477_ = crate::leanh::lean_ctor_get(v_stop_473_, 0);
        v___x_478_ = l_List_toSlice___redArg(v_list_476_, v_range_472_, v_val_477_);
        return v___x_478_;
    }
}
pub unsafe fn l_instSliceableListSliceNat__2___lam__0___boxed(
    mut v_xs_479_: *mut crate::leanh::LeanObject,
    mut v_range_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_481_ = l_instSliceableListSliceNat__2___lam__0(v_xs_479_, v_range_480_);
    crate::leanh::lean_dec_ref(v_xs_479_);
    return v_res_481_;
}
pub unsafe fn l_instSliceableListSliceNat__2(
    mut v_00_u03b1_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_484_ = l_instSliceableListSliceNat__2___closed__0;
    return v___f_484_;
}
pub unsafe fn l_instSliceableListSliceNat__3___lam__0(
    mut v_xs_485_: *mut crate::leanh::LeanObject,
    mut v_range_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_487_ = crate::leanh::lean_ctor_get(v_xs_485_, 0);
                crate::leanh::lean_inc(v_list_487_);
                v_stop_488_ = crate::leanh::lean_ctor_get(v_xs_485_, 1);
                crate::leanh::lean_inc(v_stop_488_);
                crate::leanh::lean_dec_ref(v_xs_485_);
                if crate::leanh::lean_obj_tag(v_stop_488_) == 0 {
                    v_upper_495_ = crate::leanh::lean_ctor_get(v_range_486_, 1);
                    v___x_496_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_497_ = lean_nat_add(v_upper_495_, v___x_496_);
                    v___y_490_ = v___x_497_;
                    state = 1;
                    continue;
                } else {
                    v_val_498_ = crate::leanh::lean_ctor_get(v_stop_488_, 0);
                    crate::leanh::lean_inc(v_val_498_);
                    crate::leanh::lean_dec_ref_known(v_stop_488_, 1);
                    v_upper_499_ = crate::leanh::lean_ctor_get(v_range_486_, 1);
                    v___x_500_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_501_ = lean_nat_add(v_upper_499_, v___x_500_);
                    v___x_502_ = lean_nat_dec_le(v_val_498_, v___x_501_);
                    if v___x_502_ == 0 {
                        crate::leanh::lean_dec(v_val_498_);
                        v___y_490_ = v___x_501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_501_);
                        v___y_490_ = v_val_498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lower_491_ = crate::leanh::lean_ctor_get(v_range_486_, 0);
                v___x_492_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_493_ = lean_nat_add(v_lower_491_, v___x_492_);
                v___x_494_ = l_List_toSlice___redArg(v_list_487_, v___x_493_, v___y_490_);
                crate::leanh::lean_dec(v___y_490_);
                crate::leanh::lean_dec(v_list_487_);
                return v___x_494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__3___lam__0___boxed(
    mut v_xs_503_: *mut crate::leanh::LeanObject,
    mut v_range_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_505_ = l_instSliceableListSliceNat__3___lam__0(v_xs_503_, v_range_504_);
    crate::leanh::lean_dec_ref(v_range_504_);
    return v_res_505_;
}
pub unsafe fn l_instSliceableListSliceNat__3(
    mut v_00_u03b1_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_508_ = l_instSliceableListSliceNat__3___closed__0;
    return v___f_508_;
}
pub unsafe fn l_instSliceableListSliceNat__4___lam__0(
    mut v_xs_509_: *mut crate::leanh::LeanObject,
    mut v_range_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_511_ = crate::leanh::lean_ctor_get(v_xs_509_, 0);
                v_stop_512_ = crate::leanh::lean_ctor_get(v_xs_509_, 1);
                if crate::leanh::lean_obj_tag(v_stop_512_) == 0 {
                    v_upper_519_ = crate::leanh::lean_ctor_get(v_range_510_, 1);
                    v___y_514_ = v_upper_519_;
                    state = 1;
                    continue;
                } else {
                    v_val_520_ = crate::leanh::lean_ctor_get(v_stop_512_, 0);
                    v_upper_521_ = crate::leanh::lean_ctor_get(v_range_510_, 1);
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
                v_lower_515_ = crate::leanh::lean_ctor_get(v_range_510_, 0);
                v___x_516_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_517_ = lean_nat_add(v_lower_515_, v___x_516_);
                v___x_518_ = l_List_toSlice___redArg(v_list_511_, v___x_517_, v___y_514_);
                return v___x_518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__4___lam__0___boxed(
    mut v_xs_523_: *mut crate::leanh::LeanObject,
    mut v_range_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_525_ = l_instSliceableListSliceNat__4___lam__0(v_xs_523_, v_range_524_);
    crate::leanh::lean_dec_ref(v_range_524_);
    crate::leanh::lean_dec_ref(v_xs_523_);
    return v_res_525_;
}
pub unsafe fn l_instSliceableListSliceNat__4(
    mut v_00_u03b1_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_528_ = l_instSliceableListSliceNat__4___closed__0;
    return v___f_528_;
}
pub unsafe fn l_instSliceableListSliceNat__5___lam__0(
    mut v_xs_529_: *mut crate::leanh::LeanObject,
    mut v_range_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stop_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stop_531_ = crate::leanh::lean_ctor_get(v_xs_529_, 1);
    if crate::leanh::lean_obj_tag(v_stop_531_) == 0 {
        let mut v_list_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_list_532_ = crate::leanh::lean_ctor_get(v_xs_529_, 0);
        v___x_533_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_534_ = lean_nat_add(v_range_530_, v___x_533_);
        v___x_535_ = l_List_toUnboundedSlice___redArg(v_list_532_, v___x_534_);
        return v___x_535_;
    } else {
        let mut v_list_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_list_536_ = crate::leanh::lean_ctor_get(v_xs_529_, 0);
        v_val_537_ = crate::leanh::lean_ctor_get(v_stop_531_, 0);
        v___x_538_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_539_ = lean_nat_add(v_range_530_, v___x_538_);
        v___x_540_ = l_List_toSlice___redArg(v_list_536_, v___x_539_, v_val_537_);
        return v___x_540_;
    }
}
pub unsafe fn l_instSliceableListSliceNat__5___lam__0___boxed(
    mut v_xs_541_: *mut crate::leanh::LeanObject,
    mut v_range_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_instSliceableListSliceNat__5___lam__0(v_xs_541_, v_range_542_);
    crate::leanh::lean_dec(v_range_542_);
    crate::leanh::lean_dec_ref(v_xs_541_);
    return v_res_543_;
}
pub unsafe fn l_instSliceableListSliceNat__5(
    mut v_00_u03b1_545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_546_ = l_instSliceableListSliceNat__5___closed__0;
    return v___f_546_;
}
pub unsafe fn l_instSliceableListSliceNat__6___lam__0(
    mut v_xs_547_: *mut crate::leanh::LeanObject,
    mut v_range_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_549_ = crate::leanh::lean_ctor_get(v_xs_547_, 0);
                crate::leanh::lean_inc(v_list_549_);
                v_stop_550_ = crate::leanh::lean_ctor_get(v_xs_547_, 1);
                crate::leanh::lean_inc(v_stop_550_);
                crate::leanh::lean_dec_ref(v_xs_547_);
                if crate::leanh::lean_obj_tag(v_stop_550_) == 0 {
                    v___x_555_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_556_ = lean_nat_add(v_range_548_, v___x_555_);
                    v___y_552_ = v___x_556_;
                    state = 1;
                    continue;
                } else {
                    v_val_557_ = crate::leanh::lean_ctor_get(v_stop_550_, 0);
                    crate::leanh::lean_inc(v_val_557_);
                    crate::leanh::lean_dec_ref_known(v_stop_550_, 1);
                    v___x_558_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_559_ = lean_nat_add(v_range_548_, v___x_558_);
                    v___x_560_ = lean_nat_dec_le(v_val_557_, v___x_559_);
                    if v___x_560_ == 0 {
                        crate::leanh::lean_dec(v_val_557_);
                        v___y_552_ = v___x_559_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_559_);
                        v___y_552_ = v_val_557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_553_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_554_ = l_List_toSlice___redArg(v_list_549_, v___x_553_, v___y_552_);
                crate::leanh::lean_dec(v___y_552_);
                crate::leanh::lean_dec(v_list_549_);
                return v___x_554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__6___lam__0___boxed(
    mut v_xs_561_: *mut crate::leanh::LeanObject,
    mut v_range_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_instSliceableListSliceNat__6___lam__0(v_xs_561_, v_range_562_);
    crate::leanh::lean_dec(v_range_562_);
    return v_res_563_;
}
pub unsafe fn l_instSliceableListSliceNat__6(
    mut v_00_u03b1_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_566_ = l_instSliceableListSliceNat__6___closed__0;
    return v___f_566_;
}
pub unsafe fn l_instSliceableListSliceNat__7___lam__0(
    mut v_xs_567_: *mut crate::leanh::LeanObject,
    mut v_range_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_list_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_list_569_ = crate::leanh::lean_ctor_get(v_xs_567_, 0);
                v_stop_570_ = crate::leanh::lean_ctor_get(v_xs_567_, 1);
                if crate::leanh::lean_obj_tag(v_stop_570_) == 0 {
                    v___y_572_ = v_range_568_;
                    state = 1;
                    continue;
                } else {
                    v_val_575_ = crate::leanh::lean_ctor_get(v_stop_570_, 0);
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
                v___x_573_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_574_ = l_List_toSlice___redArg(v_list_569_, v___x_573_, v___y_572_);
                return v___x_574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instSliceableListSliceNat__7___lam__0___boxed(
    mut v_xs_577_: *mut crate::leanh::LeanObject,
    mut v_range_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_579_ = l_instSliceableListSliceNat__7___lam__0(v_xs_577_, v_range_578_);
    crate::leanh::lean_dec(v_range_578_);
    crate::leanh::lean_dec_ref(v_xs_577_);
    return v_res_579_;
}
pub unsafe fn l_instSliceableListSliceNat__7(
    mut v_00_u03b1_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_582_ = l_instSliceableListSliceNat__7___closed__0;
    return v___f_582_;
}
pub unsafe fn l_instSliceableListSliceNat__8___lam__0(
    mut v_xs_583_: *mut crate::leanh::LeanObject,
    mut v_x_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_xs_583_);
    return v_xs_583_;
}
pub unsafe fn l_instSliceableListSliceNat__8___lam__0___boxed(
    mut v_xs_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_587_ = l_instSliceableListSliceNat__8___lam__0(v_xs_585_, v_x_586_);
    crate::leanh::lean_dec_ref(v_xs_585_);
    return v_res_587_;
}
pub unsafe fn l_instSliceableListSliceNat__8(
    mut v_00_u03b1_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_590_ = l_instSliceableListSliceNat__8___closed__0;
    return v___f_590_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Slice_List_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Slice_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Slice_List_Basic(
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
pub unsafe fn initialize_Init_Data_Slice_List_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Slice_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Slice_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Slice_List_Basic(builtin);
}
