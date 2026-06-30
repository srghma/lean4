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
pub static l_Std_Internal_Do_instMonadPredTrans___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__1 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__3 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__2_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__3_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__6 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__4_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__7___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__5_value: leanh::LeanClosureObject<
    2,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__9 as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__6_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__11 as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__7_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Internal_Do_instMonadPredTrans___lam__14 as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__8_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_instMonadPredTrans___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__9_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Internal_Do_instMonadPredTrans___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadPredTrans___closed__10_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadPredTrans___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadPredTrans___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadLiftPredTransForall___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Internal_Do_instMonadLiftPredTransConsForall___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Internal_Do_instPartialOrderPredTrans(
    mut v_Pred_490_: *mut leanh::LeanObject,
    mut v_EPred_491_: *mut leanh::LeanObject,
    mut v_00_u03b1_492_: *mut leanh::LeanObject,
    mut v_inst_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = leanh::lean_box(0);
    return v___x_494_;
}
pub unsafe fn l_Std_Internal_Do_instCCPOPredTrans(
    mut v_Pred_495_: *mut leanh::LeanObject,
    mut v_EPred_496_: *mut leanh::LeanObject,
    mut v_00_u03b1_497_: *mut leanh::LeanObject,
    mut v_inst_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = leanh::lean_box(0);
    return v___x_499_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__0(
    mut v_f_500_: *mut leanh::LeanObject,
    mut v___y_501_: *mut leanh::LeanObject,
    mut v_a_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_503_ = leanh::lean_apply_1(v_f_500_, v_a_502_);
    v___x_504_ = leanh::lean_apply_1(v___y_501_, v___x_503_);
    return v___x_504_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__1(
    mut v_00_u03b1_505_: *mut leanh::LeanObject,
    mut v_00_u03b2_506_: *mut leanh::LeanObject,
    mut v_f_507_: *mut leanh::LeanObject,
    mut v_x_508_: *mut leanh::LeanObject,
    mut v___y_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_511_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_511_, 0, v_f_507_);
    leanh::lean_closure_set(v___f_511_, 1, v___y_509_);
    v___x_512_ = leanh::lean_apply_2(v_x_508_, v___f_511_, v___y_510_);
    return v___x_512_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__2(
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
    mut v_a_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = leanh::lean_apply_1(v___y_513_, v___y_514_);
    return v___x_516_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__2___boxed(
    mut v___y_517_: *mut leanh::LeanObject,
    mut v___y_518_: *mut leanh::LeanObject,
    mut v_a_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Std_Internal_Do_instMonadPredTrans___lam__2(v___y_517_, v___y_518_, v_a_519_);
    leanh::lean_dec(v_a_519_);
    return v_res_520_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__3(
    mut v_00_u03b1_521_: *mut leanh::LeanObject,
    mut v_00_u03b2_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
    mut v___y_524_: *mut leanh::LeanObject,
    mut v___y_525_: *mut leanh::LeanObject,
    mut v___y_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_527_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__2___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_527_, 0, v___y_525_);
    leanh::lean_closure_set(v___f_527_, 1, v___y_523_);
    v___x_528_ = leanh::lean_apply_2(v___y_524_, v___f_527_, v___y_526_);
    return v___x_528_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__4(
    mut v_00_u03b1_529_: *mut leanh::LeanObject,
    mut v_x_530_: *mut leanh::LeanObject,
    mut v___y_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = leanh::lean_apply_1(v___y_531_, v_x_530_);
    return v___x_533_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__4___boxed(
    mut v_00_u03b1_534_: *mut leanh::LeanObject,
    mut v_x_535_: *mut leanh::LeanObject,
    mut v___y_536_: *mut leanh::LeanObject,
    mut v___y_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l_Std_Internal_Do_instMonadPredTrans___lam__4(
        v_00_u03b1_534_,
        v_x_535_,
        v___y_536_,
        v___y_537_,
    );
    leanh::lean_dec(v___y_537_);
    return v_res_538_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__5(
    mut v_f_539_: *mut leanh::LeanObject,
    mut v___y_540_: *mut leanh::LeanObject,
    mut v___y_541_: *mut leanh::LeanObject,
    mut v_a_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = leanh::lean_apply_3(v_f_539_, v_a_542_, v___y_540_, v___y_541_);
    return v___x_543_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__6(
    mut v_00_u03b1_544_: *mut leanh::LeanObject,
    mut v_00_u03b2_545_: *mut leanh::LeanObject,
    mut v_x_546_: *mut leanh::LeanObject,
    mut v_f_547_: *mut leanh::LeanObject,
    mut v___y_548_: *mut leanh::LeanObject,
    mut v___y_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_549_);
    v___f_550_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__5 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_550_, 0, v_f_547_);
    leanh::lean_closure_set(v___f_550_, 1, v___y_548_);
    leanh::lean_closure_set(v___f_550_, 2, v___y_549_);
    v___x_551_ = leanh::lean_apply_2(v_x_546_, v___f_550_, v___y_549_);
    return v___x_551_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__7(
    mut v___y_552_: *mut leanh::LeanObject,
    mut v___y_553_: *mut leanh::LeanObject,
    mut v___y_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_apply_1(v___y_553_, v___y_552_);
    return v___x_555_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__7___boxed(
    mut v___y_556_: *mut leanh::LeanObject,
    mut v___y_557_: *mut leanh::LeanObject,
    mut v___y_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_559_ = l_Std_Internal_Do_instMonadPredTrans___lam__7(v___y_556_, v___y_557_, v___y_558_);
    leanh::lean_dec(v___y_558_);
    return v_res_559_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__8(
    mut v_x_560_: *mut leanh::LeanObject,
    mut v___f_561_: *mut leanh::LeanObject,
    mut v___f_562_: *mut leanh::LeanObject,
    mut v_y_563_: *mut leanh::LeanObject,
    mut v___y_564_: *mut leanh::LeanObject,
    mut v___y_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = leanh::lean_box(0);
    v___x_567_ = leanh::lean_apply_1(v_x_560_, v___x_566_);
    v___x_568_ = leanh::lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___x_568_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_568_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_568_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_568_, 3, v___f_561_);
    leanh::lean_closure_set(v___x_568_, 4, v_y_563_);
    v___x_569_ = leanh::lean_apply_6(
        v___f_562_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_567_,
        v___x_568_,
        v___y_564_,
        v___y_565_,
    );
    return v___x_569_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__9(
    mut v___f_570_: *mut leanh::LeanObject,
    mut v___f_571_: *mut leanh::LeanObject,
    mut v_00_u03b1_572_: *mut leanh::LeanObject,
    mut v_00_u03b2_573_: *mut leanh::LeanObject,
    mut v_f_574_: *mut leanh::LeanObject,
    mut v_x_575_: *mut leanh::LeanObject,
    mut v___y_576_: *mut leanh::LeanObject,
    mut v___y_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___f_571_);
    v___f_578_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__8 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_578_, 0, v_x_575_);
    leanh::lean_closure_set(v___f_578_, 1, v___f_570_);
    leanh::lean_closure_set(v___f_578_, 2, v___f_571_);
    v___x_579_ = leanh::lean_apply_6(
        v___f_571_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_574_,
        v___f_578_,
        v___y_576_,
        v___y_577_,
    );
    return v___x_579_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__12(
    mut v_a_580_: *mut leanh::LeanObject,
    mut v_x_581_: *mut leanh::LeanObject,
    mut v___y_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_584_ = leanh::lean_apply_1(v___y_582_, v_a_580_);
    return v___x_584_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__12___boxed(
    mut v_a_585_: *mut leanh::LeanObject,
    mut v_x_586_: *mut leanh::LeanObject,
    mut v___y_587_: *mut leanh::LeanObject,
    mut v___y_588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_589_ =
        l_Std_Internal_Do_instMonadPredTrans___lam__12(v_a_585_, v_x_586_, v___y_587_, v___y_588_);
    leanh::lean_dec(v___y_588_);
    leanh::lean_dec(v_x_586_);
    return v_res_589_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__10(
    mut v_y_590_: *mut leanh::LeanObject,
    mut v___f_591_: *mut leanh::LeanObject,
    mut v_a_592_: *mut leanh::LeanObject,
    mut v___y_593_: *mut leanh::LeanObject,
    mut v___y_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_595_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__12___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_595_, 0, v_a_592_);
    v___x_596_ = leanh::lean_box(0);
    v___x_597_ = leanh::lean_apply_1(v_y_590_, v___x_596_);
    v___x_598_ = leanh::lean_apply_6(
        v___f_591_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_597_,
        v___f_595_,
        v___y_593_,
        v___y_594_,
    );
    return v___x_598_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__11(
    mut v___f_599_: *mut leanh::LeanObject,
    mut v_00_u03b1_600_: *mut leanh::LeanObject,
    mut v_00_u03b2_601_: *mut leanh::LeanObject,
    mut v_x_602_: *mut leanh::LeanObject,
    mut v_y_603_: *mut leanh::LeanObject,
    mut v___y_604_: *mut leanh::LeanObject,
    mut v___y_605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___f_599_);
    v___f_606_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__10 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_606_, 0, v_y_603_);
    leanh::lean_closure_set(v___f_606_, 1, v___f_599_);
    v___x_607_ = leanh::lean_apply_6(
        v___f_599_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_602_,
        v___f_606_,
        v___y_604_,
        v___y_605_,
    );
    return v___x_607_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__13(
    mut v_y_608_: *mut leanh::LeanObject,
    mut v___y_609_: *mut leanh::LeanObject,
    mut v___y_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = leanh::lean_box(0);
    v___x_613_ = leanh::lean_apply_3(v_y_608_, v___x_612_, v___y_609_, v___y_610_);
    return v___x_613_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__13___boxed(
    mut v_y_614_: *mut leanh::LeanObject,
    mut v___y_615_: *mut leanh::LeanObject,
    mut v___y_616_: *mut leanh::LeanObject,
    mut v_a_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ =
        l_Std_Internal_Do_instMonadPredTrans___lam__13(v_y_614_, v___y_615_, v___y_616_, v_a_617_);
    leanh::lean_dec(v_a_617_);
    return v_res_618_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans___lam__14(
    mut v_00_u03b1_619_: *mut leanh::LeanObject,
    mut v_00_u03b2_620_: *mut leanh::LeanObject,
    mut v_x_621_: *mut leanh::LeanObject,
    mut v_y_622_: *mut leanh::LeanObject,
    mut v___y_623_: *mut leanh::LeanObject,
    mut v___y_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_624_);
    v___f_625_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadPredTrans___lam__13___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_625_, 0, v_y_622_);
    leanh::lean_closure_set(v___f_625_, 1, v___y_623_);
    leanh::lean_closure_set(v___f_625_, 2, v___y_624_);
    v___x_626_ = leanh::lean_apply_2(v_x_621_, v___f_625_, v___y_624_);
    return v___x_626_;
}
pub unsafe fn l_Std_Internal_Do_instMonadPredTrans(
    mut v_Pred_650_: *mut leanh::LeanObject,
    mut v_EPred_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_652_ = l_Std_Internal_Do_instMonadPredTrans___closed__10;
    return v___x_652_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushExcept___redArg(
    mut v_post_653_: *mut leanh::LeanObject,
    mut v_epost_654_: *mut leanh::LeanObject,
    mut v_x_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_655_) == 0 {
        let mut v_a_656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_post_653_);
        v_a_656_ = leanh::lean_ctor_get(v_x_655_, 0);
        leanh::lean_inc(v_a_656_);
        leanh::lean_dec_ref_known(v_x_655_, 1);
        v_head_657_ = leanh::lean_ctor_get(v_epost_654_, 0);
        leanh::lean_inc(v_head_657_);
        leanh::lean_dec_ref(v_epost_654_);
        v___x_658_ = leanh::lean_apply_1(v_head_657_, v_a_656_);
        return v___x_658_;
    } else {
        let mut v_a_659_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_epost_654_);
        v_a_659_ = leanh::lean_ctor_get(v_x_655_, 0);
        leanh::lean_inc(v_a_659_);
        leanh::lean_dec_ref_known(v_x_655_, 1);
        v___x_660_ = leanh::lean_apply_1(v_post_653_, v_a_659_);
        return v___x_660_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushExcept(
    mut v_00_u03b1_661_: *mut leanh::LeanObject,
    mut v_00_u03b5_662_: *mut leanh::LeanObject,
    mut v_Pred_663_: *mut leanh::LeanObject,
    mut v_EPred_664_: *mut leanh::LeanObject,
    mut v_post_665_: *mut leanh::LeanObject,
    mut v_epost_666_: *mut leanh::LeanObject,
    mut v_x_667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_667_) == 0 {
        let mut v_a_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_head_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_post_665_);
        v_a_668_ = leanh::lean_ctor_get(v_x_667_, 0);
        leanh::lean_inc(v_a_668_);
        leanh::lean_dec_ref_known(v_x_667_, 1);
        v_head_669_ = leanh::lean_ctor_get(v_epost_666_, 0);
        leanh::lean_inc(v_head_669_);
        leanh::lean_dec_ref(v_epost_666_);
        v___x_670_ = leanh::lean_apply_1(v_head_669_, v_a_668_);
        return v___x_670_;
    } else {
        let mut v_a_671_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_epost_666_);
        v_a_671_ = leanh::lean_ctor_get(v_x_667_, 0);
        leanh::lean_inc(v_a_671_);
        leanh::lean_dec_ref_known(v_x_667_, 1);
        v___x_672_ = leanh::lean_apply_1(v_post_665_, v_a_671_);
        return v___x_672_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__0(
    mut v_head_673_: *mut leanh::LeanObject,
    mut v_post_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v___y_675_) == 0 {
        let mut v_a_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_post_674_);
        v_a_676_ = leanh::lean_ctor_get(v___y_675_, 0);
        leanh::lean_inc(v_a_676_);
        leanh::lean_dec_ref_known(v___y_675_, 1);
        v___x_677_ = leanh::lean_apply_1(v_head_673_, v_a_676_);
        return v___x_677_;
    } else {
        let mut v_a_678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_head_673_);
        v_a_678_ = leanh::lean_ctor_get(v___y_675_, 0);
        leanh::lean_inc(v_a_678_);
        leanh::lean_dec_ref_known(v___y_675_, 1);
        v___x_679_ = leanh::lean_apply_1(v_post_674_, v_a_678_);
        return v___x_679_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(
    mut v_x_680_: *mut leanh::LeanObject,
    mut v_post_681_: *mut leanh::LeanObject,
    mut v_epost_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_683_ = leanh::lean_ctor_get(v_epost_682_, 0);
    leanh::lean_inc(v_head_683_);
    v_tail_684_ = leanh::lean_ctor_get(v_epost_682_, 1);
    leanh::lean_inc(v_tail_684_);
    leanh::lean_dec_ref(v_epost_682_);
    v___f_685_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_685_, 0, v_head_683_);
    leanh::lean_closure_set(v___f_685_, 1, v_post_681_);
    v___x_686_ = leanh::lean_apply_2(v_x_680_, v___f_685_, v_tail_684_);
    return v___x_686_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept___redArg(
    mut v_x_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_688_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_688_, 0, v_x_687_);
    return v___f_688_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushExcept(
    mut v_00_u03b1_689_: *mut leanh::LeanObject,
    mut v_00_u03b5_690_: *mut leanh::LeanObject,
    mut v_Pred_691_: *mut leanh::LeanObject,
    mut v_EPred_692_: *mut leanh::LeanObject,
    mut v_x_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_694_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_694_, 0, v_x_693_);
    return v___f_694_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___redArg(
    mut v_post_695_: *mut leanh::LeanObject,
    mut v_epost_696_: *mut leanh::LeanObject,
    mut v_x_697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_697_) == 0 {
        let mut v_head_698_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_post_695_);
        v_head_698_ = leanh::lean_ctor_get(v_epost_696_, 0);
        leanh::lean_inc(v_head_698_);
        return v_head_698_;
    } else {
        let mut v_val_699_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_699_ = leanh::lean_ctor_get(v_x_697_, 0);
        leanh::lean_inc(v_val_699_);
        leanh::lean_dec_ref_known(v_x_697_, 1);
        v___x_700_ = leanh::lean_apply_1(v_post_695_, v_val_699_);
        return v___x_700_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___redArg___boxed(
    mut v_post_701_: *mut leanh::LeanObject,
    mut v_epost_702_: *mut leanh::LeanObject,
    mut v_x_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ =
        l_Std_Internal_Do_EPost_cons_pushOption___redArg(v_post_701_, v_epost_702_, v_x_703_);
    leanh::lean_dec_ref(v_epost_702_);
    return v_res_704_;
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption(
    mut v_00_u03b1_705_: *mut leanh::LeanObject,
    mut v_Pred_706_: *mut leanh::LeanObject,
    mut v_EPred_707_: *mut leanh::LeanObject,
    mut v_post_708_: *mut leanh::LeanObject,
    mut v_epost_709_: *mut leanh::LeanObject,
    mut v_x_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_710_) == 0 {
        let mut v_head_711_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_post_708_);
        v_head_711_ = leanh::lean_ctor_get(v_epost_709_, 0);
        leanh::lean_inc(v_head_711_);
        return v_head_711_;
    } else {
        let mut v_val_712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_712_ = leanh::lean_ctor_get(v_x_710_, 0);
        leanh::lean_inc(v_val_712_);
        leanh::lean_dec_ref_known(v_x_710_, 1);
        v___x_713_ = leanh::lean_apply_1(v_post_708_, v_val_712_);
        return v___x_713_;
    }
}
pub unsafe fn l_Std_Internal_Do_EPost_cons_pushOption___boxed(
    mut v_00_u03b1_714_: *mut leanh::LeanObject,
    mut v_Pred_715_: *mut leanh::LeanObject,
    mut v_EPred_716_: *mut leanh::LeanObject,
    mut v_post_717_: *mut leanh::LeanObject,
    mut v_epost_718_: *mut leanh::LeanObject,
    mut v_x_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Internal_Do_EPost_cons_pushOption(
        v_00_u03b1_714_,
        v_Pred_715_,
        v_EPred_716_,
        v_post_717_,
        v_epost_718_,
        v_x_719_,
    );
    leanh::lean_dec_ref(v_epost_718_);
    return v_res_720_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0(
    mut v_head_721_: *mut leanh::LeanObject,
    mut v_post_722_: *mut leanh::LeanObject,
    mut v___y_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v___y_723_) == 0 {
        leanh::lean_dec(v_post_722_);
        leanh::lean_inc(v_head_721_);
        return v_head_721_;
    } else {
        let mut v_val_724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_724_ = leanh::lean_ctor_get(v___y_723_, 0);
        leanh::lean_inc(v_val_724_);
        leanh::lean_dec_ref_known(v___y_723_, 1);
        v___x_725_ = leanh::lean_apply_1(v_post_722_, v_val_724_);
        return v___x_725_;
    }
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0___boxed(
    mut v_head_726_: *mut leanh::LeanObject,
    mut v_post_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0(
        v_head_726_,
        v_post_727_,
        v___y_728_,
    );
    leanh::lean_dec(v_head_726_);
    return v_res_729_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(
    mut v_x_730_: *mut leanh::LeanObject,
    mut v_post_731_: *mut leanh::LeanObject,
    mut v_epost_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_733_ = leanh::lean_ctor_get(v_epost_732_, 0);
    leanh::lean_inc(v_head_733_);
    v_tail_734_ = leanh::lean_ctor_get(v_epost_732_, 1);
    leanh::lean_inc(v_tail_734_);
    leanh::lean_dec_ref(v_epost_732_);
    v___f_735_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_735_, 0, v_head_733_);
    leanh::lean_closure_set(v___f_735_, 1, v_post_731_);
    v___x_736_ = leanh::lean_apply_2(v_x_730_, v___f_735_, v_tail_734_);
    return v___x_736_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption___redArg(
    mut v_x_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_738_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_738_, 0, v_x_737_);
    return v___f_738_;
}
pub unsafe fn l_Std_Internal_Do_PredTrans_pushOption(
    mut v_00_u03b1_739_: *mut leanh::LeanObject,
    mut v_Pred_740_: *mut leanh::LeanObject,
    mut v_EPred_741_: *mut leanh::LeanObject,
    mut v_x_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_743_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_743_, 0, v_x_742_);
    return v___f_743_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg___lam__0(
    mut v_post_744_: *mut leanh::LeanObject,
    mut v_x_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_746_ = leanh::lean_ctor_get(v_x_745_, 0);
    leanh::lean_inc(v_fst_746_);
    v_snd_747_ = leanh::lean_ctor_get(v_x_745_, 1);
    leanh::lean_inc(v_snd_747_);
    leanh::lean_dec_ref(v_x_745_);
    v___x_748_ = leanh::lean_apply_2(v_post_744_, v_fst_746_, v_snd_747_);
    return v___x_748_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg___lam__1(
    mut v_x_749_: *mut leanh::LeanObject,
    mut v_post_750_: *mut leanh::LeanObject,
    mut v_epost_751_: *mut leanh::LeanObject,
    mut v_s_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_753_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_753_, 0, v_post_750_);
    v___x_754_ = leanh::lean_apply_3(v_x_749_, v_s_752_, v___f_753_, v_epost_751_);
    return v___x_754_;
}
pub unsafe fn l_Std_Internal_Do_pushArg___redArg(
    mut v_x_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_756_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_756_, 0, v_x_755_);
    return v___f_756_;
}
pub unsafe fn l_Std_Internal_Do_pushArg(
    mut v_00_u03c3_757_: *mut leanh::LeanObject,
    mut v_Pred_758_: *mut leanh::LeanObject,
    mut v_EPred_759_: *mut leanh::LeanObject,
    mut v_00_u03b1_760_: *mut leanh::LeanObject,
    mut v_x_761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_762_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_pushArg___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_762_, 0, v_x_761_);
    return v___f_762_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall___lam__0(
    mut v___y_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
    mut v_a_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = leanh::lean_apply_2(v___y_763_, v_a_765_, v___y_764_);
    return v___x_766_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall___lam__1(
    mut v_00_u03b1_767_: *mut leanh::LeanObject,
    mut v_x_768_: *mut leanh::LeanObject,
    mut v___y_769_: *mut leanh::LeanObject,
    mut v___y_770_: *mut leanh::LeanObject,
    mut v___y_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_772_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadLiftPredTransForall___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_772_, 0, v___y_769_);
    leanh::lean_closure_set(v___f_772_, 1, v___y_771_);
    v___x_773_ = leanh::lean_apply_2(v_x_768_, v___f_772_, v___y_770_);
    return v___x_773_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransForall(
    mut v_00_u03c3_775_: *mut leanh::LeanObject,
    mut v_Pred_776_: *mut leanh::LeanObject,
    mut v_EPred_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_778_ = l_Std_Internal_Do_instMonadLiftPredTransForall___closed__0;
    return v___f_778_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransConsForall___lam__0(
    mut v_00_u03b1_779_: *mut leanh::LeanObject,
    mut v_x_780_: *mut leanh::LeanObject,
    mut v___y_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tail_783_ = leanh::lean_ctor_get(v___y_782_, 1);
    leanh::lean_inc(v_tail_783_);
    leanh::lean_dec_ref(v___y_782_);
    v___x_784_ = leanh::lean_apply_2(v_x_780_, v___y_781_, v_tail_783_);
    return v___x_784_;
}
pub unsafe fn l_Std_Internal_Do_instMonadLiftPredTransConsForall(
    mut v_00_u03b5_786_: *mut leanh::LeanObject,
    mut v_Pred_787_: *mut leanh::LeanObject,
    mut v_EPred_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_789_ = l_Std_Internal_Do_instMonadLiftPredTransConsForall___closed__0;
    return v___f_789_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0(
    mut v_post_790_: *mut leanh::LeanObject,
    mut v___epost_791_: *mut leanh::LeanObject,
    mut v_s_792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_792_);
    v___x_793_ = leanh::lean_apply_2(v_post_790_, v_s_792_, v_s_792_);
    return v___x_793_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0___boxed(
    mut v_post_794_: *mut leanh::LeanObject,
    mut v___epost_795_: *mut leanh::LeanObject,
    mut v_s_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__0(
        v_post_794_,
        v___epost_795_,
        v_s_796_,
    );
    leanh::lean_dec(v___epost_795_);
    return v_res_797_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1(
    mut v_s_798_: *mut leanh::LeanObject,
    mut v___y_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = leanh::lean_box(0);
    v___x_803_ = leanh::lean_apply_2(v___y_799_, v___x_802_, v_s_798_);
    return v___x_803_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1___boxed(
    mut v_s_804_: *mut leanh::LeanObject,
    mut v___y_805_: *mut leanh::LeanObject,
    mut v___y_806_: *mut leanh::LeanObject,
    mut v___y_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__1(
        v_s_804_, v___y_805_, v___y_806_, v___y_807_,
    );
    leanh::lean_dec(v___y_807_);
    leanh::lean_dec(v___y_806_);
    return v_res_808_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2(
    mut v_00_u03b1_809_: *mut leanh::LeanObject,
    mut v_f_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
    mut v___y_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = leanh::lean_apply_1(v_f_810_, v___y_813_);
    v_fst_815_ = leanh::lean_ctor_get(v___x_814_, 0);
    leanh::lean_inc(v_fst_815_);
    v_snd_816_ = leanh::lean_ctor_get(v___x_814_, 1);
    leanh::lean_inc(v_snd_816_);
    leanh::lean_dec_ref(v___x_814_);
    v___x_817_ = leanh::lean_apply_2(v___y_811_, v_fst_815_, v_snd_816_);
    return v___x_817_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2___boxed(
    mut v_00_u03b1_818_: *mut leanh::LeanObject,
    mut v_f_819_: *mut leanh::LeanObject,
    mut v___y_820_: *mut leanh::LeanObject,
    mut v___y_821_: *mut leanh::LeanObject,
    mut v___y_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___lam__2(
        v_00_u03b1_818_,
        v_f_819_,
        v___y_820_,
        v___y_821_,
        v___y_822_,
    );
    leanh::lean_dec(v___y_821_);
    return v_res_823_;
}
pub unsafe fn l_Std_Internal_Do_instMonadStateOfPredTransForall(
    mut v_00_u03c3_831_: *mut leanh::LeanObject,
    mut v_Pred_832_: *mut leanh::LeanObject,
    mut v_EPred_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__3;
    return v___x_834_;
}
pub unsafe fn l_Std_Internal_Do_instMonadReaderOfPredTransForall(
    mut v_00_u03c3_835_: *mut leanh::LeanObject,
    mut v_Pred_836_: *mut leanh::LeanObject,
    mut v_EPred_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_838_ = l_Std_Internal_Do_instMonadStateOfPredTransForall___closed__0;
    return v___f_838_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0(
    mut v_00_u03b1_839_: *mut leanh::LeanObject,
    mut v_e_840_: *mut leanh::LeanObject,
    mut v___y_841_: *mut leanh::LeanObject,
    mut v___y_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_head_843_ = leanh::lean_ctor_get(v___y_842_, 0);
    leanh::lean_inc(v_head_843_);
    leanh::lean_dec_ref(v___y_842_);
    v___x_844_ = leanh::lean_apply_1(v_head_843_, v_e_840_);
    return v___x_844_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0___boxed(
    mut v_00_u03b1_845_: *mut leanh::LeanObject,
    mut v_e_846_: *mut leanh::LeanObject,
    mut v___y_847_: *mut leanh::LeanObject,
    mut v___y_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_849_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__0(
        v_00_u03b1_845_,
        v_e_846_,
        v___y_847_,
        v___y_848_,
    );
    leanh::lean_dec(v___y_847_);
    return v_res_849_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__1(
    mut v_handle_850_: *mut leanh::LeanObject,
    mut v___y_851_: *mut leanh::LeanObject,
    mut v___y_852_: *mut leanh::LeanObject,
    mut v_e_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = leanh::lean_apply_3(v_handle_850_, v_e_853_, v___y_851_, v___y_852_);
    return v___x_854_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__2(
    mut v_00_u03b1_855_: *mut leanh::LeanObject,
    mut v_x_856_: *mut leanh::LeanObject,
    mut v_handle_857_: *mut leanh::LeanObject,
    mut v___y_858_: *mut leanh::LeanObject,
    mut v___y_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tail_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tail_860_ = leanh::lean_ctor_get(v___y_859_, 1);
    leanh::lean_inc(v_tail_860_);
    leanh::lean_inc(v___y_858_);
    v___f_861_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_861_, 0, v_handle_857_);
    leanh::lean_closure_set(v___f_861_, 1, v___y_858_);
    leanh::lean_closure_set(v___f_861_, 2, v___y_859_);
    v___x_862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_862_, 0, v___f_861_);
    leanh::lean_ctor_set(v___x_862_, 1, v_tail_860_);
    v___x_863_ = leanh::lean_apply_2(v_x_856_, v___y_858_, v___x_862_);
    return v___x_863_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall(
    mut v_00_u03b5_869_: *mut leanh::LeanObject,
    mut v_Pred_870_: *mut leanh::LeanObject,
    mut v_EPred_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall___closed__2;
    return v___x_872_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__0(
    mut v___y_873_: *mut leanh::LeanObject,
    mut v___y_874_: *mut leanh::LeanObject,
    mut v_x_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = leanh::lean_apply_2(v___y_873_, v_x_875_, v___y_874_);
    return v___x_876_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__1(
    mut v_inst_877_: *mut leanh::LeanObject,
    mut v_00_u03b1_878_: *mut leanh::LeanObject,
    mut v_x_879_: *mut leanh::LeanObject,
    mut v___y_880_: *mut leanh::LeanObject,
    mut v___y_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_883_ = leanh::lean_ctor_get(v_inst_877_, 0);
    leanh::lean_inc(v_throw_883_);
    leanh::lean_dec_ref(v_inst_877_);
    v___f_884_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_884_, 0, v___y_880_);
    leanh::lean_closure_set(v___f_884_, 1, v___y_882_);
    v___x_885_ = leanh::lean_apply_4(
        v_throw_883_,
        leanh::lean_box(0),
        v_x_879_,
        v___f_884_,
        v___y_881_,
    );
    return v___x_885_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__2(
    mut v___y_886_: *mut leanh::LeanObject,
    mut v_rs_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_888_ = leanh::lean_ctor_get(v_rs_887_, 0);
    leanh::lean_inc(v_fst_888_);
    v_snd_889_ = leanh::lean_ctor_get(v_rs_887_, 1);
    leanh::lean_inc(v_snd_889_);
    leanh::lean_dec_ref(v_rs_887_);
    v___x_890_ = leanh::lean_apply_2(v___y_886_, v_fst_888_, v_snd_889_);
    return v___x_890_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__3(
    mut v___y_891_: *mut leanh::LeanObject,
    mut v_r_892_: *mut leanh::LeanObject,
    mut v_s_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_894_, 0, v_r_892_);
    leanh::lean_ctor_set(v___x_894_, 1, v_s_893_);
    v___x_895_ = leanh::lean_apply_1(v___y_891_, v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__4(
    mut v_handle_896_: *mut leanh::LeanObject,
    mut v___y_897_: *mut leanh::LeanObject,
    mut v_e_898_: *mut leanh::LeanObject,
    mut v___y_899_: *mut leanh::LeanObject,
    mut v___y_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_901_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__3
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_901_, 0, v___y_899_);
    v___x_902_ =
        leanh::lean_apply_4(v_handle_896_, v_e_898_, v___f_901_, v___y_900_, v___y_897_);
    return v___x_902_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__5(
    mut v_post_903_: *mut leanh::LeanObject,
    mut v_r_904_: *mut leanh::LeanObject,
    mut v_s_905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_906_, 0, v_r_904_);
    leanh::lean_ctor_set(v___x_906_, 1, v_s_905_);
    v___x_907_ = leanh::lean_apply_1(v_post_903_, v___x_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__6(
    mut v_x_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v_post_910_: *mut leanh::LeanObject,
    mut v_epost_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_912_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__5
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_912_, 0, v_post_910_);
    v___x_913_ = leanh::lean_apply_3(v_x_908_, v___f_912_, v_epost_911_, v___y_909_);
    return v___x_913_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__7(
    mut v_inst_914_: *mut leanh::LeanObject,
    mut v_00_u03b1_915_: *mut leanh::LeanObject,
    mut v_x_916_: *mut leanh::LeanObject,
    mut v_handle_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_921_ = leanh::lean_ctor_get(v_inst_914_, 1);
    leanh::lean_inc(v_tryCatch_921_);
    leanh::lean_dec_ref(v_inst_914_);
    v___f_922_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__2
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_922_, 0, v___y_918_);
    leanh::lean_inc(v___y_920_);
    v___f_923_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__4
            as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_923_, 0, v_handle_917_);
    leanh::lean_closure_set(v___f_923_, 1, v___y_920_);
    v___f_924_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__6
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_924_, 0, v_x_916_);
    leanh::lean_closure_set(v___f_924_, 1, v___y_920_);
    v___x_925_ = leanh::lean_apply_5(
        v_tryCatch_921_,
        leanh::lean_box(0),
        v___f_924_,
        v___f_923_,
        v___f_922_,
        v___y_919_,
    );
    return v___x_925_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg(
    mut v_inst_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_926_);
    v___f_927_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_927_, 0, v_inst_926_);
    v___f_928_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg___lam__7
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_928_, 0, v_inst_926_);
    v___x_929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_929_, 0, v___f_927_);
    leanh::lean_ctor_set(v___x_929_, 1, v___f_928_);
    return v___x_929_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransForall(
    mut v_00_u03b5_930_: *mut leanh::LeanObject,
    mut v_Pred_931_: *mut leanh::LeanObject,
    mut v_EPred_932_: *mut leanh::LeanObject,
    mut v_00_u03c3_933_: *mut leanh::LeanObject,
    mut v_inst_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_935_ = l_Std_Internal_Do_instMonadExceptOfPredTransForall___redArg(v_inst_934_);
    return v___x_935_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__0(
    mut v_inst_936_: *mut leanh::LeanObject,
    mut v_00_u03b1_937_: *mut leanh::LeanObject,
    mut v_x_938_: *mut leanh::LeanObject,
    mut v___y_939_: *mut leanh::LeanObject,
    mut v___y_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_941_ = leanh::lean_ctor_get(v_inst_936_, 0);
    leanh::lean_inc(v_throw_941_);
    leanh::lean_dec_ref(v_inst_936_);
    v_tail_942_ = leanh::lean_ctor_get(v___y_940_, 1);
    leanh::lean_inc(v_tail_942_);
    leanh::lean_dec_ref(v___y_940_);
    v___x_943_ = leanh::lean_apply_4(
        v_throw_941_,
        leanh::lean_box(0),
        v_x_938_,
        v___y_939_,
        v_tail_942_,
    );
    return v___x_943_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__1(
    mut v_head_944_: *mut leanh::LeanObject,
    mut v_handle_945_: *mut leanh::LeanObject,
    mut v_e_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_949_, 0, v_head_944_);
    leanh::lean_ctor_set(v___x_949_, 1, v___y_948_);
    v___x_950_ = leanh::lean_apply_3(v_handle_945_, v_e_946_, v___y_947_, v___x_949_);
    return v___x_950_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__2(
    mut v_head_951_: *mut leanh::LeanObject,
    mut v_x_952_: *mut leanh::LeanObject,
    mut v_post_x27_953_: *mut leanh::LeanObject,
    mut v_epost_x27_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_955_, 0, v_head_951_);
    leanh::lean_ctor_set(v___x_955_, 1, v_epost_x27_954_);
    v___x_956_ = leanh::lean_apply_2(v_x_952_, v_post_x27_953_, v___x_955_);
    return v___x_956_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__3(
    mut v_inst_957_: *mut leanh::LeanObject,
    mut v_00_u03b1_958_: *mut leanh::LeanObject,
    mut v_x_959_: *mut leanh::LeanObject,
    mut v_handle_960_: *mut leanh::LeanObject,
    mut v___y_961_: *mut leanh::LeanObject,
    mut v___y_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_963_ = leanh::lean_ctor_get(v_inst_957_, 1);
    leanh::lean_inc(v_tryCatch_963_);
    leanh::lean_dec_ref(v_inst_957_);
    v_head_964_ = leanh::lean_ctor_get(v___y_962_, 0);
    leanh::lean_inc_n(v_head_964_, 2);
    v_tail_965_ = leanh::lean_ctor_get(v___y_962_, 1);
    leanh::lean_inc(v_tail_965_);
    leanh::lean_dec_ref(v___y_962_);
    v___f_966_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_966_, 0, v_head_964_);
    leanh::lean_closure_set(v___f_966_, 1, v_handle_960_);
    v___f_967_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_967_, 0, v_head_964_);
    leanh::lean_closure_set(v___f_967_, 1, v_x_959_);
    v___x_968_ = leanh::lean_apply_5(
        v_tryCatch_963_,
        leanh::lean_box(0),
        v___f_967_,
        v___f_966_,
        v___y_961_,
        v_tail_965_,
    );
    return v___x_968_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg(
    mut v_inst_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_969_);
    v___f_970_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_970_, 0, v_inst_969_);
    v___f_971_ = leanh::lean_alloc_closure(
        l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg___lam__3
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_971_, 0, v_inst_969_);
    v___x_972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_972_, 0, v___f_970_);
    leanh::lean_ctor_set(v___x_972_, 1, v___f_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1(
    mut v_00_u03b5_973_: *mut leanh::LeanObject,
    mut v_Pred_974_: *mut leanh::LeanObject,
    mut v_EPred_975_: *mut leanh::LeanObject,
    mut v_00_u03b5_x27_976_: *mut leanh::LeanObject,
    mut v_inst_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l_Std_Internal_Do_instMonadExceptOfPredTransConsForall__1___redArg(v_inst_977_);
    return v___x_978_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_PredTrans(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_ExceptPost(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_PredTrans(
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
pub unsafe fn initialize_Std_Internal_Do_PredTrans(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Assertion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Do_ExceptPost(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_PredTrans(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_PredTrans(builtin);
}