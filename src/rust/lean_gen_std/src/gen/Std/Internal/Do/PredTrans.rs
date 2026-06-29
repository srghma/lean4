// Lean compiler output
// Module: Std.Internal.Do.PredTrans
// Imports: Std.Internal.Do.Assertion Std.Internal.Do.ExceptPost
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::r#gen::Std::Internal::Do::Assertion::{
    initialize_Std_Internal_Do_Assertion, runtime_initialize_Std_Internal_Do_Assertion,
};
use crate::r#gen::Std::Internal::Do::ExceptPost::{
    initialize_Std_Internal_Do_ExceptPost, runtime_initialize_Std_Internal_Do_ExceptPost,
};
pub static l_Std_Internal_Do_instMonadPredTrans___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__3 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__6 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__4_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__7___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__5_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__9 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__6_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__11 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__7_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__14 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__8_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_instMonadPredTrans___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__9_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_instMonadPredTrans___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__10_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadLiftPredTransForall___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadLiftPredTransConsForall___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__2
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Internal_Do_instPartialOrderPredTrans(
    mut v_Pred_490_: *mut crate::leanh::LeanObject,
    mut v_EPred_491_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_492_: *mut crate::leanh::LeanObject,
    mut v_inst_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = crate::leanh::lean_box(0);
    return v___x_494_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOPredTrans(
    mut v_Pred_495_: *mut crate::leanh::LeanObject,
    mut v_EPred_496_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_497_: *mut crate::leanh::LeanObject,
    mut v_inst_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = crate::leanh::lean_box(0);
    return v___x_499_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__0(
    mut v_f_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
    mut v_a_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = crate::leanh::lean_apply_1(v_f_500_, v_a_502_);
    v___x_504_ = crate::leanh::lean_apply_1(v___y_501_, v___x_503_);
    return v___x_504_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__1(
    mut v_00_u03b1_505_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_506_: *mut crate::leanh::LeanObject,
    mut v_f_507_: *mut crate::leanh::LeanObject,
    mut v_x_508_: *mut crate::leanh::LeanObject,
    mut v___y_509_: *mut crate::leanh::LeanObject,
    mut v___y_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_511_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_511_, 0, v_f_507_);
    crate::leanh::lean_closure_set(v___f_511_, 1, v___y_509_);
    v___x_512_ = crate::leanh::lean_apply_2(v_x_508_, v___f_511_, v___y_510_);
    return v___x_512_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__2(
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = crate::leanh::lean_apply_1(v___y_513_, v___y_514_);
    return v___x_516_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__2___boxed(
    mut v___y_517_: *mut crate::leanh::LeanObject,
    mut v___y_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Std_Internal_Do_instMonadPredTrans___lam__2(v___y_517_, v___y_518_, v_a_519_);
    crate::leanh::lean_dec(v_a_519_);
    return v_res_520_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__3(
    mut v_00_u03b1_521_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_522_: *mut crate::leanh::LeanObject,
    mut v___y_523_: *mut crate::leanh::LeanObject,
    mut v___y_524_: *mut crate::leanh::LeanObject,
    mut v___y_525_: *mut crate::leanh::LeanObject,
    mut v___y_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_527_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__2___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_527_, 0, v___y_525_);
    crate::leanh::lean_closure_set(v___f_527_, 1, v___y_523_);
    v___x_528_ = crate::leanh::lean_apply_2(v___y_524_, v___f_527_, v___y_526_);
    return v___x_528_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__4(
    mut v_00_u03b1_529_: *mut crate::leanh::LeanObject,
    mut v_x_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
    mut v___y_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = crate::leanh::lean_apply_1(v___y_531_, v_x_530_);
    return v___x_533_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__4___boxed(
    mut v_00_u03b1_534_: *mut crate::leanh::LeanObject,
    mut v_x_535_: *mut crate::leanh::LeanObject,
    mut v___y_536_: *mut crate::leanh::LeanObject,
    mut v___y_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_Internal_Do_instMonadPredTrans___lam__4(
        v_00_u03b1_534_,
        v_x_535_,
        v___y_536_,
        v___y_537_,
    );
    crate::leanh::lean_dec(v___y_537_);
    return v_res_538_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__5(
    mut v_f_539_: *mut crate::leanh::LeanObject,
    mut v___y_540_: *mut crate::leanh::LeanObject,
    mut v___y_541_: *mut crate::leanh::LeanObject,
    mut v_a_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = crate::leanh::lean_apply_3(v_f_539_, v_a_542_, v___y_540_, v___y_541_);
    return v___x_543_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__6(
    mut v_00_u03b1_544_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_545_: *mut crate::leanh::LeanObject,
    mut v_x_546_: *mut crate::leanh::LeanObject,
    mut v_f_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
    mut v___y_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_549_);
    v___f_550_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_550_, 0, v_f_547_);
    crate::leanh::lean_closure_set(v___f_550_, 1, v___y_548_);
    crate::leanh::lean_closure_set(v___f_550_, 2, v___y_549_);
    v___x_551_ = crate::leanh::lean_apply_2(v_x_546_, v___f_550_, v___y_549_);
    return v___x_551_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__7(
    mut v___y_552_: *mut crate::leanh::LeanObject,
    mut v___y_553_: *mut crate::leanh::LeanObject,
    mut v___y_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = crate::leanh::lean_apply_1(v___y_553_, v___y_552_);
    return v___x_555_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__7___boxed(
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Std_Internal_Do_instMonadPredTrans___lam__7(v___y_556_, v___y_557_, v___y_558_);
    crate::leanh::lean_dec(v___y_558_);
    return v_res_559_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__8(
    mut v_x_560_: *mut crate::leanh::LeanObject,
    mut v___f_561_: *mut crate::leanh::LeanObject,
    mut v___f_562_: *mut crate::leanh::LeanObject,
    mut v_y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = crate::leanh::lean_box(0);
    v___x_567_ = crate::leanh::lean_apply_1(v_x_560_, v___x_566_);
    v___x_568_ = crate::leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___x_568_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_568_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_568_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_568_, 3, v___f_561_);
    crate::leanh::lean_closure_set(v___x_568_, 4, v_y_563_);
    v___x_569_ = crate::leanh::lean_apply_6(
        v___f_562_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_567_,
        v___x_568_,
        v___y_564_,
        v___y_565_,
    );
    return v___x_569_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__9(
    mut v___f_570_: *mut crate::leanh::LeanObject,
    mut v___f_571_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_572_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_573_: *mut crate::leanh::LeanObject,
    mut v_f_574_: *mut crate::leanh::LeanObject,
    mut v_x_575_: *mut crate::leanh::LeanObject,
    mut v___y_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___f_571_);
    v___f_578_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__8 as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_578_, 0, v_x_575_);
    crate::leanh::lean_closure_set(v___f_578_, 1, v___f_570_);
    crate::leanh::lean_closure_set(v___f_578_, 2, v___f_571_);
    v___x_579_ = crate::leanh::lean_apply_6(
        v___f_571_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_f_574_,
        v___f_578_,
        v___y_576_,
        v___y_577_,
    );
    return v___x_579_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__12(
    mut v_a_580_: *mut crate::leanh::LeanObject,
    mut v_x_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = crate::leanh::lean_apply_1(v___y_582_, v_a_580_);
    return v___x_584_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__12___boxed(
    mut v_a_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
    mut v___y_587_: *mut crate::leanh::LeanObject,
    mut v___y_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_589_ =
        l_Std_Internal_Do_instMonadPredTrans___lam__12(v_a_585_, v_x_586_, v___y_587_, v___y_588_);
    crate::leanh::lean_dec(v___y_588_);
    crate::leanh::lean_dec(v_x_586_);
    return v_res_589_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__10(
    mut v_y_590_: *mut crate::leanh::LeanObject,
    mut v___f_591_: *mut crate::leanh::LeanObject,
    mut v_a_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_595_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__12___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_595_, 0, v_a_592_);
    v___x_596_ = crate::leanh::lean_box(0);
    v___x_597_ = crate::leanh::lean_apply_1(v_y_590_, v___x_596_);
    v___x_598_ = crate::leanh::lean_apply_6(
        v___f_591_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_597_,
        v___f_595_,
        v___y_593_,
        v___y_594_,
    );
    return v___x_598_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__11(
    mut v___f_599_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_600_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_601_: *mut crate::leanh::LeanObject,
    mut v_x_602_: *mut crate::leanh::LeanObject,
    mut v_y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___f_599_);
    v___f_606_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__10 as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_606_, 0, v_y_603_);
    crate::leanh::lean_closure_set(v___f_606_, 1, v___f_599_);
    v___x_607_ = crate::leanh::lean_apply_6(
        v___f_599_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_602_,
        v___f_606_,
        v___y_604_,
        v___y_605_,
    );
    return v___x_607_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__13(
    mut v_y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v_a_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = crate::leanh::lean_box(0);
    v___x_613_ = crate::leanh::lean_apply_3(v_y_608_, v___x_612_, v___y_609_, v___y_610_);
    return v___x_613_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__13___boxed(
    mut v_y_614_: *mut crate::leanh::LeanObject,
    mut v___y_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
    mut v_a_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ =
        l_Std_Internal_Do_instMonadPredTrans___lam__13(v_y_614_, v___y_615_, v___y_616_, v_a_617_);
    crate::leanh::lean_dec(v_a_617_);
    return v_res_618_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__14(
    mut v_00_u03b1_619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_620_: *mut crate::leanh::LeanObject,
    mut v_x_621_: *mut crate::leanh::LeanObject,
    mut v_y_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_624_);
    v___f_625_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__13___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_625_, 0, v_y_622_);
    crate::leanh::lean_closure_set(v___f_625_, 1, v___y_623_);
    crate::leanh::lean_closure_set(v___f_625_, 2, v___y_624_);
    v___x_626_ = crate::leanh::lean_apply_2(v_x_621_, v___f_625_, v___y_624_);
    return v___x_626_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans(
    mut v_Pred_650_: *mut crate::leanh::LeanObject,
    mut v_EPred_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Std_Internal_Do_instMonadPredTrans___closed__10;
    return v___x_652_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushExcept___redArg(
    mut v_post_653_: *mut crate::leanh::LeanObject,
    mut v_epost_654_: *mut crate::leanh::LeanObject,
    mut v_x_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_655_) == 0 {
        let mut v_a_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_post_653_);
        v_a_656_ = crate::leanh::lean_ctor_get(v_x_655_, 0);
        crate::leanh::lean_inc(v_a_656_);
        crate::leanh::lean_dec_ref_known(v_x_655_, 1);
        v_head_657_ = crate::leanh::lean_ctor_get(v_epost_654_, 0);
        crate::leanh::lean_inc(v_head_657_);
        crate::leanh::lean_dec_ref(v_epost_654_);
        v___x_658_ = crate::leanh::lean_apply_1(v_head_657_, v_a_656_);
        return v___x_658_;
    } else {
        let mut v_a_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_epost_654_);
        v_a_659_ = crate::leanh::lean_ctor_get(v_x_655_, 0);
        crate::leanh::lean_inc(v_a_659_);
        crate::leanh::lean_dec_ref_known(v_x_655_, 1);
        v___x_660_ = crate::leanh::lean_apply_1(v_post_653_, v_a_659_);
        return v___x_660_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushExcept(
    mut v_00_u03b1_661_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_662_: *mut crate::leanh::LeanObject,
    mut v_Pred_663_: *mut crate::leanh::LeanObject,
    mut v_EPred_664_: *mut crate::leanh::LeanObject,
    mut v_post_665_: *mut crate::leanh::LeanObject,
    mut v_epost_666_: *mut crate::leanh::LeanObject,
    mut v_x_667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_667_) == 0 {
        let mut v_a_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_post_665_);
        v_a_668_ = crate::leanh::lean_ctor_get(v_x_667_, 0);
        crate::leanh::lean_inc(v_a_668_);
        crate::leanh::lean_dec_ref_known(v_x_667_, 1);
        v_head_669_ = crate::leanh::lean_ctor_get(v_epost_666_, 0);
        crate::leanh::lean_inc(v_head_669_);
        crate::leanh::lean_dec_ref(v_epost_666_);
        v___x_670_ = crate::leanh::lean_apply_1(v_head_669_, v_a_668_);
        return v___x_670_;
    } else {
        let mut v_a_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_epost_666_);
        v_a_671_ = crate::leanh::lean_ctor_get(v_x_667_, 0);
        crate::leanh::lean_inc(v_a_671_);
        crate::leanh::lean_dec_ref_known(v_x_667_, 1);
        v___x_672_ = crate::leanh::lean_apply_1(v_post_665_, v_a_671_);
        return v___x_672_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__0(
    mut v_head_673_: *mut crate::leanh::LeanObject,
    mut v_post_674_: *mut crate::leanh::LeanObject,
    mut v___y_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v___y_675_) == 0 {
        let mut v_a_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_post_674_);
        v_a_676_ = crate::leanh::lean_ctor_get(v___y_675_, 0);
        crate::leanh::lean_inc(v_a_676_);
        crate::leanh::lean_dec_ref_known(v___y_675_, 1);
        v___x_677_ = crate::leanh::lean_apply_1(v_head_673_, v_a_676_);
        return v___x_677_;
    } else {
        let mut v_a_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_head_673_);
        v_a_678_ = crate::leanh::lean_ctor_get(v___y_675_, 0);
        crate::leanh::lean_inc(v_a_678_);
        crate::leanh::lean_dec_ref_known(v___y_675_, 1);
        v___x_679_ = crate::leanh::lean_apply_1(v_post_674_, v_a_678_);
        return v___x_679_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(
    mut v_x_680_: *mut crate::leanh::LeanObject,
    mut v_post_681_: *mut crate::leanh::LeanObject,
    mut v_epost_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_683_ = crate::leanh::lean_ctor_get(v_epost_682_, 0);
    crate::leanh::lean_inc(v_head_683_);
    v_tail_684_ = crate::leanh::lean_ctor_get(v_epost_682_, 1);
    crate::leanh::lean_inc(v_tail_684_);
    crate::leanh::lean_dec_ref(v_epost_682_);
    v___f_685_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_685_, 0, v_head_683_);
    crate::leanh::lean_closure_set(v___f_685_, 1, v_post_681_);
    v___x_686_ = crate::leanh::lean_apply_2(v_x_680_, v___f_685_, v_tail_684_);
    return v___x_686_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg(
    mut v_x_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_688_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_688_, 0, v_x_687_);
    return v___f_688_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept(
    mut v_00_u03b1_689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_690_: *mut crate::leanh::LeanObject,
    mut v_Pred_691_: *mut crate::leanh::LeanObject,
    mut v_EPred_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_694_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_694_, 0, v_x_693_);
    return v___f_694_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___redArg(
    mut v_post_695_: *mut crate::leanh::LeanObject,
    mut v_epost_696_: *mut crate::leanh::LeanObject,
    mut v_x_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_697_) == 0 {
        let mut v_head_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_post_695_);
        v_head_698_ = crate::leanh::lean_ctor_get(v_epost_696_, 0);
        crate::leanh::lean_inc(v_head_698_);
        return v_head_698_;
    } else {
        let mut v_val_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_699_ = crate::leanh::lean_ctor_get(v_x_697_, 0);
        crate::leanh::lean_inc(v_val_699_);
        crate::leanh::lean_dec_ref_known(v_x_697_, 1);
        v___x_700_ = crate::leanh::lean_apply_1(v_post_695_, v_val_699_);
        return v___x_700_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___redArg___boxed(
    mut v_post_701_: *mut crate::leanh::LeanObject,
    mut v_epost_702_: *mut crate::leanh::LeanObject,
    mut v_x_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ =
        l_Std_Internal_Do_EPost_cons_pushOption___redArg(v_post_701_, v_epost_702_, v_x_703_);
    crate::leanh::lean_dec_ref(v_epost_702_);
    return v_res_704_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption(
    mut v_00_u03b1_705_: *mut crate::leanh::LeanObject,
    mut v_Pred_706_: *mut crate::leanh::LeanObject,
    mut v_EPred_707_: *mut crate::leanh::LeanObject,
    mut v_post_708_: *mut crate::leanh::LeanObject,
    mut v_epost_709_: *mut crate::leanh::LeanObject,
    mut v_x_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_710_) == 0 {
        let mut v_head_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_post_708_);
        v_head_711_ = crate::leanh::lean_ctor_get(v_epost_709_, 0);
        crate::leanh::lean_inc(v_head_711_);
        return v_head_711_;
    } else {
        let mut v_val_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_712_ = crate::leanh::lean_ctor_get(v_x_710_, 0);
        crate::leanh::lean_inc(v_val_712_);
        crate::leanh::lean_dec_ref_known(v_x_710_, 1);
        v___x_713_ = crate::leanh::lean_apply_1(v_post_708_, v_val_712_);
        return v___x_713_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___boxed(
    mut v_00_u03b1_714_: *mut crate::leanh::LeanObject,
    mut v_Pred_715_: *mut crate::leanh::LeanObject,
    mut v_EPred_716_: *mut crate::leanh::LeanObject,
    mut v_post_717_: *mut crate::leanh::LeanObject,
    mut v_epost_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Internal_Do_EPost_cons_pushOption(
        v_00_u03b1_714_,
        v_Pred_715_,
        v_EPred_716_,
        v_post_717_,
        v_epost_718_,
        v_x_719_,
    );
    crate::leanh::lean_dec_ref(v_epost_718_);
    return v_res_720_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0(
    mut v_head_721_: *mut crate::leanh::LeanObject,
    mut v_post_722_: *mut crate::leanh::LeanObject,
    mut v___y_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v___y_723_) == 0 {
        crate::leanh::lean_dec(v_post_722_);
        crate::leanh::lean_inc(v_head_721_);
        return v_head_721_;
    } else {
        let mut v_val_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_724_ = crate::leanh::lean_ctor_get(v___y_723_, 0);
        crate::leanh::lean_inc(v_val_724_);
        crate::leanh::lean_dec_ref_known(v___y_723_, 1);
        v___x_725_ = crate::leanh::lean_apply_1(v_post_722_, v_val_724_);
        return v___x_725_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0___boxed(
    mut v_head_726_: *mut crate::leanh::LeanObject,
    mut v_post_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0(
        v_head_726_,
        v_post_727_,
        v___y_728_,
    );
    crate::leanh::lean_dec(v_head_726_);
    return v_res_729_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(
    mut v_x_730_: *mut crate::leanh::LeanObject,
    mut v_post_731_: *mut crate::leanh::LeanObject,
    mut v_epost_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_733_ = crate::leanh::lean_ctor_get(v_epost_732_, 0);
    crate::leanh::lean_inc(v_head_733_);
    v_tail_734_ = crate::leanh::lean_ctor_get(v_epost_732_, 1);
    crate::leanh::lean_inc(v_tail_734_);
    crate::leanh::lean_dec_ref(v_epost_732_);
    v___f_735_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_735_, 0, v_head_733_);
    crate::leanh::lean_closure_set(v___f_735_, 1, v_post_731_);
    v___x_736_ = crate::leanh::lean_apply_2(v_x_730_, v___f_735_, v_tail_734_);
    return v___x_736_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg(
    mut v_x_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_738_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_738_, 0, v_x_737_);
    return v___f_738_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption(
    mut v_00_u03b1_739_: *mut crate::leanh::LeanObject,
    mut v_Pred_740_: *mut crate::leanh::LeanObject,
    mut v_EPred_741_: *mut crate::leanh::LeanObject,
    mut v_x_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_743_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_743_, 0, v_x_742_);
    return v___f_743_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg___lam__0(
    mut v_post_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_746_ = crate::leanh::lean_ctor_get(v_x_745_, 0);
    crate::leanh::lean_inc(v_fst_746_);
    v_snd_747_ = crate::leanh::lean_ctor_get(v_x_745_, 1);
    crate::leanh::lean_inc(v_snd_747_);
    crate::leanh::lean_dec_ref(v_x_745_);
    v___x_748_ = crate::leanh::lean_apply_2(v_post_744_, v_fst_746_, v_snd_747_);
    return v___x_748_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg___lam__1(
    mut v_x_749_: *mut crate::leanh::LeanObject,
    mut v_post_750_: *mut crate::leanh::LeanObject,
    mut v_epost_751_: *mut crate::leanh::LeanObject,
    mut v_s_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_753_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_753_, 0, v_post_750_);
    v___x_754_ = crate::leanh::lean_apply_3(v_x_749_, v_s_752_, v___f_753_, v_epost_751_);
    return v___x_754_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg(
    mut v_x_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_756_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_756_, 0, v_x_755_);
    return v___f_756_;
}
pub unsafe fn l_Std_Internal_Do_pushArg(
    mut v_00_u03c3_757_: *mut crate::leanh::LeanObject,
    mut v_Pred_758_: *mut crate::leanh::LeanObject,
    mut v_EPred_759_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_760_: *mut crate::leanh::LeanObject,
    mut v_x_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_762_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_762_, 0, v_x_761_);
    return v___f_762_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall___lam__0(
    mut v___y_763_: *mut crate::leanh::LeanObject,
    mut v___y_764_: *mut crate::leanh::LeanObject,
    mut v_a_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = crate::leanh::lean_apply_2(v___y_763_, v_a_765_, v___y_764_);
    return v___x_766_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall___lam__1(
    mut v_00_u03b1_767_: *mut crate::leanh::LeanObject,
    mut v_x_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_772_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadLiftPredTransForall___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_772_, 0, v___y_769_);
    crate::leanh::lean_closure_set(v___f_772_, 1, v___y_771_);
    v___x_773_ = crate::leanh::lean_apply_2(v_x_768_, v___f_772_, v___y_770_);
    return v___x_773_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall(
    mut v_00_u03c3_775_: *mut crate::leanh::LeanObject,
    mut v_Pred_776_: *mut crate::leanh::LeanObject,
    mut v_EPred_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_778_ = l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0;
    return v___f_778_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransConsForall___lam__0(
    mut v_00_u03b1_779_: *mut crate::leanh::LeanObject,
    mut v_x_780_: *mut crate::leanh::LeanObject,
    mut v___y_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tail_783_ = crate::leanh::lean_ctor_get(v___y_782_, 1);
    crate::leanh::lean_inc(v_tail_783_);
    crate::leanh::lean_dec_ref(v___y_782_);
    v___x_784_ = crate::leanh::lean_apply_2(v_x_780_, v___y_781_, v_tail_783_);
    return v___x_784_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransConsForall(
    mut v_00_u03b5_786_: *mut crate::leanh::LeanObject,
    mut v_Pred_787_: *mut crate::leanh::LeanObject,
    mut v_EPred_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_789_ = l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0;
    return v___f_789_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0(
    mut v_post_790_: *mut crate::leanh::LeanObject,
    mut v___epost_791_: *mut crate::leanh::LeanObject,
    mut v_s_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_792_);
    v___x_793_ = crate::leanh::lean_apply_2(v_post_790_, v_s_792_, v_s_792_);
    return v___x_793_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0___boxed(
    mut v_post_794_: *mut crate::leanh::LeanObject,
    mut v___epost_795_: *mut crate::leanh::LeanObject,
    mut v_s_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0(
        v_post_794_,
        v___epost_795_,
        v_s_796_,
    );
    crate::leanh::lean_dec(v___epost_795_);
    return v_res_797_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1(
    mut v_s_798_: *mut crate::leanh::LeanObject,
    mut v___y_799_: *mut crate::leanh::LeanObject,
    mut v___y_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = crate::leanh::lean_box(0);
    v___x_803_ = crate::leanh::lean_apply_2(v___y_799_, v___x_802_, v_s_798_);
    return v___x_803_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1___boxed(
    mut v_s_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1(
        v_s_804_, v___y_805_, v___y_806_, v___y_807_,
    );
    crate::leanh::lean_dec(v___y_807_);
    crate::leanh::lean_dec(v___y_806_);
    return v_res_808_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2(
    mut v_00_u03b1_809_: *mut crate::leanh::LeanObject,
    mut v_f_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
    mut v___y_812_: *mut crate::leanh::LeanObject,
    mut v___y_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = crate::leanh::lean_apply_1(v_f_810_, v___y_813_);
    v_fst_815_ = crate::leanh::lean_ctor_get(v___x_814_, 0);
    crate::leanh::lean_inc(v_fst_815_);
    v_snd_816_ = crate::leanh::lean_ctor_get(v___x_814_, 1);
    crate::leanh::lean_inc(v_snd_816_);
    crate::leanh::lean_dec_ref(v___x_814_);
    v___x_817_ = crate::leanh::lean_apply_2(v___y_811_, v_fst_815_, v_snd_816_);
    return v___x_817_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2___boxed(
    mut v_00_u03b1_818_: *mut crate::leanh::LeanObject,
    mut v_f_819_: *mut crate::leanh::LeanObject,
    mut v___y_820_: *mut crate::leanh::LeanObject,
    mut v___y_821_: *mut crate::leanh::LeanObject,
    mut v___y_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2(
        v_00_u03b1_818_,
        v_f_819_,
        v___y_820_,
        v___y_821_,
        v___y_822_,
    );
    crate::leanh::lean_dec(v___y_821_);
    return v_res_823_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall(
    mut v_00_u03c3_831_: *mut crate::leanh::LeanObject,
    mut v_Pred_832_: *mut crate::leanh::LeanObject,
    mut v_EPred_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3;
    return v___x_834_;
}
pub unsafe fn l_Std_Internal_Do_instMonadReaderOfPredTransForall(
    mut v_00_u03c3_835_: *mut crate::leanh::LeanObject,
    mut v_Pred_836_: *mut crate::leanh::LeanObject,
    mut v_EPred_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_838_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0;
    return v___f_838_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0(
    mut v_00_u03b1_839_: *mut crate::leanh::LeanObject,
    mut v_e_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_head_843_ = crate::leanh::lean_ctor_get(v___y_842_, 0);
    crate::leanh::lean_inc(v_head_843_);
    crate::leanh::lean_dec_ref(v___y_842_);
    v___x_844_ = crate::leanh::lean_apply_1(v_head_843_, v_e_840_);
    return v___x_844_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0___boxed(
    mut v_00_u03b1_845_: *mut crate::leanh::LeanObject,
    mut v_e_846_: *mut crate::leanh::LeanObject,
    mut v___y_847_: *mut crate::leanh::LeanObject,
    mut v___y_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0(
        v_00_u03b1_845_,
        v_e_846_,
        v___y_847_,
        v___y_848_,
    );
    crate::leanh::lean_dec(v___y_847_);
    return v_res_849_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__1(
    mut v_handle_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v_e_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = crate::leanh::lean_apply_3(v_handle_850_, v_e_853_, v___y_851_, v___y_852_);
    return v___x_854_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__2(
    mut v_00_u03b1_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
    mut v_handle_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tail_860_ = crate::leanh::lean_ctor_get(v___y_859_, 1);
    crate::leanh::lean_inc(v_tail_860_);
    crate::leanh::lean_inc(v___y_858_);
    v___f_861_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_861_, 0, v_handle_857_);
    crate::leanh::lean_closure_set(v___f_861_, 1, v___y_858_);
    crate::leanh::lean_closure_set(v___f_861_, 2, v___y_859_);
    v___x_862_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_862_, 0, v___f_861_);
    crate::leanh::lean_ctor_set(v___x_862_, 1, v_tail_860_);
    v___x_863_ = crate::leanh::lean_apply_2(v_x_856_, v___y_858_, v___x_862_);
    return v___x_863_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall(
    mut v_00_u03b5_869_: *mut crate::leanh::LeanObject,
    mut v_Pred_870_: *mut crate::leanh::LeanObject,
    mut v_EPred_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2;
    return v___x_872_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__0(
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v_x_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = crate::leanh::lean_apply_2(v___y_873_, v_x_875_, v___y_874_);
    return v___x_876_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__1(
    mut v_inst_877_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_x_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_883_ = crate::leanh::lean_ctor_get(v_inst_877_, 0);
    crate::leanh::lean_inc(v_throw_883_);
    crate::leanh::lean_dec_ref(v_inst_877_);
    v___f_884_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_884_, 0, v___y_880_);
    crate::leanh::lean_closure_set(v___f_884_, 1, v___y_882_);
    v___x_885_ = crate::leanh::lean_apply_4(
        v_throw_883_,
        crate::leanh::lean_box(0),
        v_x_879_,
        v___f_884_,
        v___y_881_,
    );
    return v___x_885_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__2(
    mut v___y_886_: *mut crate::leanh::LeanObject,
    mut v_rs_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_888_ = crate::leanh::lean_ctor_get(v_rs_887_, 0);
    crate::leanh::lean_inc(v_fst_888_);
    v_snd_889_ = crate::leanh::lean_ctor_get(v_rs_887_, 1);
    crate::leanh::lean_inc(v_snd_889_);
    crate::leanh::lean_dec_ref(v_rs_887_);
    v___x_890_ = crate::leanh::lean_apply_2(v___y_886_, v_fst_888_, v_snd_889_);
    return v___x_890_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__3(
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v_r_892_: *mut crate::leanh::LeanObject,
    mut v_s_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_894_, 0, v_r_892_);
    crate::leanh::lean_ctor_set(v___x_894_, 1, v_s_893_);
    v___x_895_ = crate::leanh::lean_apply_1(v___y_891_, v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__4(
    mut v_handle_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v_e_898_: *mut crate::leanh::LeanObject,
    mut v___y_899_: *mut crate::leanh::LeanObject,
    mut v___y_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_901_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__3
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_901_, 0, v___y_899_);
    v___x_902_ =
        crate::leanh::lean_apply_4(v_handle_896_, v_e_898_, v___f_901_, v___y_900_, v___y_897_);
    return v___x_902_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__5(
    mut v_post_903_: *mut crate::leanh::LeanObject,
    mut v_r_904_: *mut crate::leanh::LeanObject,
    mut v_s_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_906_, 0, v_r_904_);
    crate::leanh::lean_ctor_set(v___x_906_, 1, v_s_905_);
    v___x_907_ = crate::leanh::lean_apply_1(v_post_903_, v___x_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__6(
    mut v_x_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v_post_910_: *mut crate::leanh::LeanObject,
    mut v_epost_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_912_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__5
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_912_, 0, v_post_910_);
    v___x_913_ = crate::leanh::lean_apply_3(v_x_908_, v___f_912_, v_epost_911_, v___y_909_);
    return v___x_913_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__7(
    mut v_inst_914_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_915_: *mut crate::leanh::LeanObject,
    mut v_x_916_: *mut crate::leanh::LeanObject,
    mut v_handle_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_921_ = crate::leanh::lean_ctor_get(v_inst_914_, 1);
    crate::leanh::lean_inc(v_tryCatch_921_);
    crate::leanh::lean_dec_ref(v_inst_914_);
    v___f_922_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__2
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_922_, 0, v___y_918_);
    crate::leanh::lean_inc(v___y_920_);
    v___f_923_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__4
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_923_, 0, v_handle_917_);
    crate::leanh::lean_closure_set(v___f_923_, 1, v___y_920_);
    v___f_924_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__6
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_924_, 0, v_x_916_);
    crate::leanh::lean_closure_set(v___f_924_, 1, v___y_920_);
    v___x_925_ = crate::leanh::lean_apply_5(
        v_tryCatch_921_,
        crate::leanh::lean_box(0),
        v___f_924_,
        v___f_923_,
        v___f_922_,
        v___y_919_,
    );
    return v___x_925_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg(
    mut v_inst_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_926_);
    v___f_927_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_927_, 0, v_inst_926_);
    v___f_928_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__7
            as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_928_, 0, v_inst_926_);
    v___x_929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_929_, 0, v___f_927_);
    crate::leanh::lean_ctor_set(v___x_929_, 1, v___f_928_);
    return v___x_929_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall(
    mut v_00_u03b5_930_: *mut crate::leanh::LeanObject,
    mut v_Pred_931_: *mut crate::leanh::LeanObject,
    mut v_EPred_932_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_933_: *mut crate::leanh::LeanObject,
    mut v_inst_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg(v_inst_934_);
    return v___x_935_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__0(
    mut v_inst_936_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_937_: *mut crate::leanh::LeanObject,
    mut v_x_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
    mut v___y_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_throw_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_throw_941_ = crate::leanh::lean_ctor_get(v_inst_936_, 0);
    crate::leanh::lean_inc(v_throw_941_);
    crate::leanh::lean_dec_ref(v_inst_936_);
    v_tail_942_ = crate::leanh::lean_ctor_get(v___y_940_, 1);
    crate::leanh::lean_inc(v_tail_942_);
    crate::leanh::lean_dec_ref(v___y_940_);
    v___x_943_ = crate::leanh::lean_apply_4(
        v_throw_941_,
        crate::leanh::lean_box(0),
        v_x_938_,
        v___y_939_,
        v_tail_942_,
    );
    return v___x_943_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__1(
    mut v_head_944_: *mut crate::leanh::LeanObject,
    mut v_handle_945_: *mut crate::leanh::LeanObject,
    mut v_e_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_949_, 0, v_head_944_);
    crate::leanh::lean_ctor_set(v___x_949_, 1, v___y_948_);
    v___x_950_ = crate::leanh::lean_apply_3(v_handle_945_, v_e_946_, v___y_947_, v___x_949_);
    return v___x_950_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__2(
    mut v_head_951_: *mut crate::leanh::LeanObject,
    mut v_x_952_: *mut crate::leanh::LeanObject,
    mut v_post_x27_953_: *mut crate::leanh::LeanObject,
    mut v_epost_x27_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_955_, 0, v_head_951_);
    crate::leanh::lean_ctor_set(v___x_955_, 1, v_epost_x27_954_);
    v___x_956_ = crate::leanh::lean_apply_2(v_x_952_, v_post_x27_953_, v___x_955_);
    return v___x_956_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__3(
    mut v_inst_957_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_958_: *mut crate::leanh::LeanObject,
    mut v_x_959_: *mut crate::leanh::LeanObject,
    mut v_handle_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tryCatch_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_963_ = crate::leanh::lean_ctor_get(v_inst_957_, 1);
    crate::leanh::lean_inc(v_tryCatch_963_);
    crate::leanh::lean_dec_ref(v_inst_957_);
    v_head_964_ = crate::leanh::lean_ctor_get(v___y_962_, 0);
    crate::leanh::lean_inc_n(v_head_964_, 2);
    v_tail_965_ = crate::leanh::lean_ctor_get(v___y_962_, 1);
    crate::leanh::lean_inc(v_tail_965_);
    crate::leanh::lean_dec_ref(v___y_962_);
    v___f_966_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_966_, 0, v_head_964_);
    crate::leanh::lean_closure_set(v___f_966_, 1, v_handle_960_);
    v___f_967_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_967_, 0, v_head_964_);
    crate::leanh::lean_closure_set(v___f_967_, 1, v_x_959_);
    v___x_968_ = crate::leanh::lean_apply_5(
        v_tryCatch_963_,
        crate::leanh::lean_box(0),
        v___f_967_,
        v___f_966_,
        v___y_961_,
        v_tail_965_,
    );
    return v___x_968_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg(
    mut v_inst_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_inst_969_);
    v___f_970_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_970_, 0, v_inst_969_);
    v___f_971_ = crate::leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__3
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_971_, 0, v_inst_969_);
    v___x_972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_972_, 0, v___f_970_);
    crate::leanh::lean_ctor_set(v___x_972_, 1, v___f_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1(
    mut v_00_u03b5_973_: *mut crate::leanh::LeanObject,
    mut v_Pred_974_: *mut crate::leanh::LeanObject,
    mut v_EPred_975_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_x27_976_: *mut crate::leanh::LeanObject,
    mut v_inst_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg(v_inst_977_);
    return v___x_978_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_PredTrans(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_PredTrans(
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
pub unsafe fn initialize_Std_Internal_Do_PredTrans(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Assertion(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Do_ExceptPost(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_PredTrans(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_PredTrans(builtin);
}
