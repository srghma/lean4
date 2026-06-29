// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: Init.Control.Basic Init.Grind.Tactics
use crate::r#gen::Init::Control::Basic::{
    initialize_Init_Control_Basic, runtime_initialize_Init_Control_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::l_Option_map;
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l_Option_mapM___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_mapM___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Option_mapM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_mapM___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_instOrElse___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_instOrElse___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Option_instOrElse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_instOrElse___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_toArray___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Option_toArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_toArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instFunctorOption___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFunctorOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instFunctorOption___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_map as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFunctorOption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instFunctorOption___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instFunctorOption___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instFunctorOption___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instFunctorOption___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_instFunctorOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__4_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_instFunctorOption___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadOption___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_bind as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadOption___closed__6_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadOption___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadOption___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut crate::leanh::LeanObject;
pub static mut l_instMonadOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_instAlternativeOption___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instAlternativeOption___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAlternativeOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instAlternativeOption___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instAlternativeOption___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAlternativeOption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instAlternativeOption___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instMonadOption___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instAlternativeOption___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instAlternativeOption___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instAlternativeOption___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut crate::leanh::LeanObject;
pub static mut l_instAlternativeOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadExceptOfUnitOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_tryCatch___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instMonadExceptOfUnitOption___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_instMonadExceptOfUnitOption: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_instDecidableEq___redArg(
    mut v_inst_730_: *mut crate::leanh::LeanObject,
    mut v_a_731_: *mut crate::leanh::LeanObject,
    mut v_b_732_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_a_731_) == 0 {
        crate::leanh::lean_dec_ref(v_inst_730_);
        if crate::leanh::lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_733_: u8 = 0;
            v___x_733_ = 1;
            return v___x_733_;
        } else {
            let mut v___x_734_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_b_732_, 1);
            v___x_734_ = 0;
            return v___x_734_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_735_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_a_731_, 1);
            crate::leanh::lean_dec_ref(v_inst_730_);
            v___x_735_ = 0;
            return v___x_735_;
        } else {
            let mut v_val_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_739_: u8 = 0;
            v_val_736_ = crate::leanh::lean_ctor_get(v_a_731_, 0);
            crate::leanh::lean_inc(v_val_736_);
            crate::leanh::lean_dec_ref_known(v_a_731_, 1);
            v_val_737_ = crate::leanh::lean_ctor_get(v_b_732_, 0);
            crate::leanh::lean_inc(v_val_737_);
            crate::leanh::lean_dec_ref_known(v_b_732_, 1);
            v___x_738_ = crate::leanh::lean_apply_2(v_inst_730_, v_val_736_, v_val_737_);
            v___x_739_ = (crate::leanh::lean_unbox(v___x_738_) as u8);
            return v___x_739_;
        }
    }
}
pub unsafe fn l_Option_instDecidableEq___redArg___boxed(
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_b_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_743_: u8 = 0;
    let mut v_r_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_743_ = l_Option_instDecidableEq___redArg(v_inst_740_, v_a_741_, v_b_742_);
    v_r_744_ = crate::leanh::lean_box((v_res_743_) as usize);
    return v_r_744_;
}
pub unsafe fn l_Option_instDecidableEq(
    mut v_00_u03b1_745_: *mut crate::leanh::LeanObject,
    mut v_inst_746_: *mut crate::leanh::LeanObject,
    mut v_a_747_: *mut crate::leanh::LeanObject,
    mut v_b_748_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_749_: u8 = 0;
    v___x_749_ = l_Option_instDecidableEq___redArg(v_inst_746_, v_a_747_, v_b_748_);
    return v___x_749_;
}
pub unsafe fn l_Option_instDecidableEq___boxed(
    mut v_00_u03b1_750_: *mut crate::leanh::LeanObject,
    mut v_inst_751_: *mut crate::leanh::LeanObject,
    mut v_a_752_: *mut crate::leanh::LeanObject,
    mut v_b_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_754_: u8 = 0;
    let mut v_r_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Option_instDecidableEq(v_00_u03b1_750_, v_inst_751_, v_a_752_, v_b_753_);
    v_r_755_ = crate::leanh::lean_box((v_res_754_) as usize);
    return v_r_755_;
}
pub unsafe fn l_Option_decidableEqNone___redArg(mut v_o_756_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_o_756_) == 0 {
        let mut v___x_757_: u8 = 0;
        v___x_757_ = 1;
        return v___x_757_;
    } else {
        let mut v___x_758_: u8 = 0;
        v___x_758_ = 0;
        return v___x_758_;
    }
}
pub unsafe fn l_Option_decidableEqNone___redArg___boxed(
    mut v_o_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Option_decidableEqNone___redArg(v_o_759_);
    crate::leanh::lean_dec(v_o_759_);
    v_r_761_ = crate::leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_Option_decidableEqNone(
    mut v_00_u03b1_762_: *mut crate::leanh::LeanObject,
    mut v_o_763_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_764_: u8 = 0;
    v___x_764_ = l_Option_decidableEqNone___redArg(v_o_763_);
    return v___x_764_;
}
pub unsafe fn l_Option_decidableEqNone___boxed(
    mut v_00_u03b1_765_: *mut crate::leanh::LeanObject,
    mut v_o_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_767_: u8 = 0;
    let mut v_r_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Option_decidableEqNone(v_00_u03b1_765_, v_o_766_);
    crate::leanh::lean_dec(v_o_766_);
    v_r_768_ = crate::leanh::lean_box((v_res_767_) as usize);
    return v_r_768_;
}
pub unsafe fn l_Option_decidableNoneEq___redArg(mut v_o_769_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_o_769_) == 0 {
        let mut v___x_770_: u8 = 0;
        v___x_770_ = 1;
        return v___x_770_;
    } else {
        let mut v___x_771_: u8 = 0;
        v___x_771_ = 0;
        return v___x_771_;
    }
}
pub unsafe fn l_Option_decidableNoneEq___redArg___boxed(
    mut v_o_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: u8 = 0;
    let mut v_r_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Option_decidableNoneEq___redArg(v_o_772_);
    crate::leanh::lean_dec(v_o_772_);
    v_r_774_ = crate::leanh::lean_box((v_res_773_) as usize);
    return v_r_774_;
}
pub unsafe fn l_Option_decidableNoneEq(
    mut v_00_u03b1_775_: *mut crate::leanh::LeanObject,
    mut v_o_776_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_777_: u8 = 0;
    v___x_777_ = l_Option_decidableNoneEq___redArg(v_o_776_);
    return v___x_777_;
}
pub unsafe fn l_Option_decidableNoneEq___boxed(
    mut v_00_u03b1_778_: *mut crate::leanh::LeanObject,
    mut v_o_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Option_decidableNoneEq(v_00_u03b1_778_, v_o_779_);
    crate::leanh::lean_dec(v_o_779_);
    v_r_781_ = crate::leanh::lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Option_instBEq_beq___redArg(
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_x_783_: *mut crate::leanh::LeanObject,
    mut v_x_784_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_783_) == 0 {
        crate::leanh::lean_dec_ref(v_inst_782_);
        if crate::leanh::lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_785_: u8 = 0;
            v___x_785_ = 1;
            return v___x_785_;
        } else {
            let mut v___x_786_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_784_, 1);
            v___x_786_ = 0;
            return v___x_786_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_787_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_783_, 1);
            crate::leanh::lean_dec_ref(v_inst_782_);
            v___x_787_ = 0;
            return v___x_787_;
        } else {
            let mut v_val_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v_val_788_ = crate::leanh::lean_ctor_get(v_x_783_, 0);
            crate::leanh::lean_inc(v_val_788_);
            crate::leanh::lean_dec_ref_known(v_x_783_, 1);
            v_val_789_ = crate::leanh::lean_ctor_get(v_x_784_, 0);
            crate::leanh::lean_inc(v_val_789_);
            crate::leanh::lean_dec_ref_known(v_x_784_, 1);
            v___x_790_ = crate::leanh::lean_apply_2(v_inst_782_, v_val_788_, v_val_789_);
            v___x_791_ = (crate::leanh::lean_unbox(v___x_790_) as u8);
            return v___x_791_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___redArg___boxed(
    mut v_inst_792_: *mut crate::leanh::LeanObject,
    mut v_x_793_: *mut crate::leanh::LeanObject,
    mut v_x_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: u8 = 0;
    let mut v_r_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Option_instBEq_beq___redArg(v_inst_792_, v_x_793_, v_x_794_);
    v_r_796_ = crate::leanh::lean_box((v_res_795_) as usize);
    return v_r_796_;
}
pub unsafe fn l_Option_instBEq_beq(
    mut v_00_u03b1_797_: *mut crate::leanh::LeanObject,
    mut v_inst_798_: *mut crate::leanh::LeanObject,
    mut v_x_799_: *mut crate::leanh::LeanObject,
    mut v_x_800_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_801_: u8 = 0;
    v___x_801_ = l_Option_instBEq_beq___redArg(v_inst_798_, v_x_799_, v_x_800_);
    return v___x_801_;
}
pub unsafe fn l_Option_instBEq_beq___boxed(
    mut v_00_u03b1_802_: *mut crate::leanh::LeanObject,
    mut v_inst_803_: *mut crate::leanh::LeanObject,
    mut v_x_804_: *mut crate::leanh::LeanObject,
    mut v_x_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Option_instBEq_beq(v_00_u03b1_802_, v_inst_803_, v_x_804_, v_x_805_);
    v_r_807_ = crate::leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Option_instBEq___redArg(
    mut v_inst_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = crate::leanh::lean_alloc_closure(
        l_Option_instBEq_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_809_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_809_, 1, v_inst_808_);
    return v___x_809_;
}
pub unsafe fn l_Option_instBEq(
    mut v_00_u03b1_810_: *mut crate::leanh::LeanObject,
    mut v_inst_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = crate::leanh::lean_alloc_closure(
        l_Option_instBEq_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_812_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_812_, 1, v_inst_811_);
    return v___x_812_;
}
pub unsafe fn l_Option_getM___redArg(
    mut v_inst_813_: *mut crate::leanh::LeanObject,
    mut v_x_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_814_) == 0 {
        let mut v_failure_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_failure_815_ = crate::leanh::lean_ctor_get(v_inst_813_, 1);
        crate::leanh::lean_inc(v_failure_815_);
        crate::leanh::lean_dec_ref(v_inst_813_);
        v___x_816_ = crate::leanh::lean_apply_1(v_failure_815_, crate::leanh::lean_box(0));
        return v___x_816_;
    } else {
        let mut v_toApplicative_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_817_ = crate::leanh::lean_ctor_get(v_inst_813_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_817_);
        crate::leanh::lean_dec_ref(v_inst_813_);
        v_toPure_818_ = crate::leanh::lean_ctor_get(v_toApplicative_817_, 1);
        crate::leanh::lean_inc(v_toPure_818_);
        crate::leanh::lean_dec_ref(v_toApplicative_817_);
        v_val_819_ = crate::leanh::lean_ctor_get(v_x_814_, 0);
        crate::leanh::lean_inc(v_val_819_);
        crate::leanh::lean_dec_ref_known(v_x_814_, 1);
        v___x_820_ =
            crate::leanh::lean_apply_2(v_toPure_818_, crate::leanh::lean_box(0), v_val_819_);
        return v___x_820_;
    }
}
pub unsafe fn l_Option_getM(
    mut v_m_821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_822_: *mut crate::leanh::LeanObject,
    mut v_inst_823_: *mut crate::leanh::LeanObject,
    mut v_x_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = l_Option_getM___redArg(v_inst_823_, v_x_824_);
    return v___x_825_;
}
pub unsafe fn l_Option_isSome___redArg(mut v_x_826_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_826_) == 0 {
        let mut v___x_827_: u8 = 0;
        v___x_827_ = 0;
        return v___x_827_;
    } else {
        let mut v___x_828_: u8 = 0;
        v___x_828_ = 1;
        return v___x_828_;
    }
}
pub unsafe fn l_Option_isSome___redArg___boxed(
    mut v_x_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_830_: u8 = 0;
    let mut v_r_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Option_isSome___redArg(v_x_829_);
    crate::leanh::lean_dec(v_x_829_);
    v_r_831_ = crate::leanh::lean_box((v_res_830_) as usize);
    return v_r_831_;
}
pub unsafe fn l_Option_isSome(
    mut v_00_u03b1_832_: *mut crate::leanh::LeanObject,
    mut v_x_833_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_833_) == 0 {
        let mut v___x_834_: u8 = 0;
        v___x_834_ = 0;
        return v___x_834_;
    } else {
        let mut v___x_835_: u8 = 0;
        v___x_835_ = 1;
        return v___x_835_;
    }
}
pub unsafe fn l_Option_isSome___boxed(
    mut v_00_u03b1_836_: *mut crate::leanh::LeanObject,
    mut v_x_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Option_isSome(v_00_u03b1_836_, v_x_837_);
    crate::leanh::lean_dec(v_x_837_);
    v_r_839_ = crate::leanh::lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_Option_isNone___redArg(mut v_x_840_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_840_) == 0 {
        let mut v___x_841_: u8 = 0;
        v___x_841_ = 1;
        return v___x_841_;
    } else {
        let mut v___x_842_: u8 = 0;
        v___x_842_ = 0;
        return v___x_842_;
    }
}
pub unsafe fn l_Option_isNone___redArg___boxed(
    mut v_x_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: u8 = 0;
    let mut v_r_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Option_isNone___redArg(v_x_843_);
    crate::leanh::lean_dec(v_x_843_);
    v_r_845_ = crate::leanh::lean_box((v_res_844_) as usize);
    return v_r_845_;
}
pub unsafe fn l_Option_isNone(
    mut v_00_u03b1_846_: *mut crate::leanh::LeanObject,
    mut v_x_847_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_847_) == 0 {
        let mut v___x_848_: u8 = 0;
        v___x_848_ = 1;
        return v___x_848_;
    } else {
        let mut v___x_849_: u8 = 0;
        v___x_849_ = 0;
        return v___x_849_;
    }
}
pub unsafe fn l_Option_isNone___boxed(
    mut v_00_u03b1_850_: *mut crate::leanh::LeanObject,
    mut v_x_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_852_: u8 = 0;
    let mut v_r_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Option_isNone(v_00_u03b1_850_, v_x_851_);
    crate::leanh::lean_dec(v_x_851_);
    v_r_853_ = crate::leanh::lean_box((v_res_852_) as usize);
    return v_r_853_;
}
pub unsafe fn l_Option_isEqSome___redArg(
    mut v_inst_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_855_) == 0 {
        let mut v___x_857_: u8 = 0;
        crate::leanh::lean_dec(v_x_856_);
        crate::leanh::lean_dec_ref(v_inst_854_);
        v___x_857_ = 0;
        return v___x_857_;
    } else {
        let mut v_val_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: u8 = 0;
        v_val_858_ = crate::leanh::lean_ctor_get(v_x_855_, 0);
        crate::leanh::lean_inc(v_val_858_);
        crate::leanh::lean_dec_ref_known(v_x_855_, 1);
        v___x_859_ = crate::leanh::lean_apply_2(v_inst_854_, v_val_858_, v_x_856_);
        v___x_860_ = (crate::leanh::lean_unbox(v___x_859_) as u8);
        return v___x_860_;
    }
}
pub unsafe fn l_Option_isEqSome___redArg___boxed(
    mut v_inst_861_: *mut crate::leanh::LeanObject,
    mut v_x_862_: *mut crate::leanh::LeanObject,
    mut v_x_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_864_: u8 = 0;
    let mut v_r_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Option_isEqSome___redArg(v_inst_861_, v_x_862_, v_x_863_);
    v_r_865_ = crate::leanh::lean_box((v_res_864_) as usize);
    return v_r_865_;
}
pub unsafe fn l_Option_isEqSome(
    mut v_00_u03b1_866_: *mut crate::leanh::LeanObject,
    mut v_inst_867_: *mut crate::leanh::LeanObject,
    mut v_x_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_868_) == 0 {
        let mut v___x_870_: u8 = 0;
        crate::leanh::lean_dec(v_x_869_);
        crate::leanh::lean_dec_ref(v_inst_867_);
        v___x_870_ = 0;
        return v___x_870_;
    } else {
        let mut v_val_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: u8 = 0;
        v_val_871_ = crate::leanh::lean_ctor_get(v_x_868_, 0);
        crate::leanh::lean_inc(v_val_871_);
        crate::leanh::lean_dec_ref_known(v_x_868_, 1);
        v___x_872_ = crate::leanh::lean_apply_2(v_inst_867_, v_val_871_, v_x_869_);
        v___x_873_ = (crate::leanh::lean_unbox(v___x_872_) as u8);
        return v___x_873_;
    }
}
pub unsafe fn l_Option_isEqSome___boxed(
    mut v_00_u03b1_874_: *mut crate::leanh::LeanObject,
    mut v_inst_875_: *mut crate::leanh::LeanObject,
    mut v_x_876_: *mut crate::leanh::LeanObject,
    mut v_x_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_878_: u8 = 0;
    let mut v_r_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Option_isEqSome(v_00_u03b1_874_, v_inst_875_, v_x_876_, v_x_877_);
    v_r_879_ = crate::leanh::lean_box((v_res_878_) as usize);
    return v_r_879_;
}
pub unsafe fn l_Option_bind___redArg(
    mut v_x_880_: *mut crate::leanh::LeanObject,
    mut v_x_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_880_) == 0 {
        let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_x_881_);
        v___x_882_ = crate::leanh::lean_box(0);
        return v___x_882_;
    } else {
        let mut v_val_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_883_ = crate::leanh::lean_ctor_get(v_x_880_, 0);
        crate::leanh::lean_inc(v_val_883_);
        crate::leanh::lean_dec_ref_known(v_x_880_, 1);
        v___x_884_ = crate::leanh::lean_apply_1(v_x_881_, v_val_883_);
        return v___x_884_;
    }
}
pub unsafe fn l_Option_bind(
    mut v_00_u03b1_885_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_886_: *mut crate::leanh::LeanObject,
    mut v_x_887_: *mut crate::leanh::LeanObject,
    mut v_x_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_887_) == 0 {
        let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_x_888_);
        v___x_889_ = crate::leanh::lean_box(0);
        return v___x_889_;
    } else {
        let mut v_val_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_890_ = crate::leanh::lean_ctor_get(v_x_887_, 0);
        crate::leanh::lean_inc(v_val_890_);
        crate::leanh::lean_dec_ref_known(v_x_887_, 1);
        v___x_891_ = crate::leanh::lean_apply_1(v_x_888_, v_val_890_);
        return v___x_891_;
    }
}
pub unsafe fn l_Option_bindM___redArg(
    mut v_inst_892_: *mut crate::leanh::LeanObject,
    mut v_f_893_: *mut crate::leanh::LeanObject,
    mut v_x_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_894_) == 0 {
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_893_);
        v___x_895_ = crate::leanh::lean_box(0);
        v___x_896_ = crate::leanh::lean_apply_2(v_inst_892_, crate::leanh::lean_box(0), v___x_895_);
        return v___x_896_;
    } else {
        let mut v_val_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_892_);
        v_val_897_ = crate::leanh::lean_ctor_get(v_x_894_, 0);
        crate::leanh::lean_inc(v_val_897_);
        crate::leanh::lean_dec_ref_known(v_x_894_, 1);
        v___x_898_ = crate::leanh::lean_apply_1(v_f_893_, v_val_897_);
        return v___x_898_;
    }
}
pub unsafe fn l_Option_bindM(
    mut v_m_899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_900_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_901_: *mut crate::leanh::LeanObject,
    mut v_inst_902_: *mut crate::leanh::LeanObject,
    mut v_f_903_: *mut crate::leanh::LeanObject,
    mut v_x_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_904_) == 0 {
        let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_903_);
        v___x_905_ = crate::leanh::lean_box(0);
        v___x_906_ = crate::leanh::lean_apply_2(v_inst_902_, crate::leanh::lean_box(0), v___x_905_);
        return v___x_906_;
    } else {
        let mut v_val_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_inst_902_);
        v_val_907_ = crate::leanh::lean_ctor_get(v_x_904_, 0);
        crate::leanh::lean_inc(v_val_907_);
        crate::leanh::lean_dec_ref_known(v_x_904_, 1);
        v___x_908_ = crate::leanh::lean_apply_1(v_f_903_, v_val_907_);
        return v___x_908_;
    }
}
pub unsafe fn l_Option_mapM___redArg___lam__0(
    mut v_val_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_910_, 0, v_val_909_);
    return v___x_910_;
}
pub unsafe fn l_Option_mapM___redArg(
    mut v_inst_912_: *mut crate::leanh::LeanObject,
    mut v_f_913_: *mut crate::leanh::LeanObject,
    mut v_x_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_914_) == 0 {
        let mut v_toPure_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_913_);
        v_toPure_915_ = crate::leanh::lean_ctor_get(v_inst_912_, 1);
        crate::leanh::lean_inc(v_toPure_915_);
        crate::leanh::lean_dec_ref(v_inst_912_);
        v___x_916_ = crate::leanh::lean_box(0);
        v___x_917_ =
            crate::leanh::lean_apply_2(v_toPure_915_, crate::leanh::lean_box(0), v___x_916_);
        return v___x_917_;
    } else {
        let mut v_toFunctor_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_918_ = crate::leanh::lean_ctor_get(v_inst_912_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_918_);
        crate::leanh::lean_dec_ref(v_inst_912_);
        v_val_919_ = crate::leanh::lean_ctor_get(v_x_914_, 0);
        crate::leanh::lean_inc(v_val_919_);
        crate::leanh::lean_dec_ref_known(v_x_914_, 1);
        v_map_920_ = crate::leanh::lean_ctor_get(v_toFunctor_918_, 0);
        crate::leanh::lean_inc(v_map_920_);
        crate::leanh::lean_dec_ref(v_toFunctor_918_);
        v___f_921_ = l_Option_mapM___redArg___closed__0;
        v___x_922_ = crate::leanh::lean_apply_1(v_f_913_, v_val_919_);
        v___x_923_ = crate::leanh::lean_apply_4(
            v_map_920_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_921_,
            v___x_922_,
        );
        return v___x_923_;
    }
}
pub unsafe fn l_Option_mapM(
    mut v_m_924_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_925_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_926_: *mut crate::leanh::LeanObject,
    mut v_inst_927_: *mut crate::leanh::LeanObject,
    mut v_f_928_: *mut crate::leanh::LeanObject,
    mut v_x_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_929_) == 0 {
        let mut v_toPure_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_928_);
        v_toPure_930_ = crate::leanh::lean_ctor_get(v_inst_927_, 1);
        crate::leanh::lean_inc(v_toPure_930_);
        crate::leanh::lean_dec_ref(v_inst_927_);
        v___x_931_ = crate::leanh::lean_box(0);
        v___x_932_ =
            crate::leanh::lean_apply_2(v_toPure_930_, crate::leanh::lean_box(0), v___x_931_);
        return v___x_932_;
    } else {
        let mut v_toFunctor_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_933_ = crate::leanh::lean_ctor_get(v_inst_927_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_933_);
        crate::leanh::lean_dec_ref(v_inst_927_);
        v_val_934_ = crate::leanh::lean_ctor_get(v_x_929_, 0);
        crate::leanh::lean_inc(v_val_934_);
        crate::leanh::lean_dec_ref_known(v_x_929_, 1);
        v_map_935_ = crate::leanh::lean_ctor_get(v_toFunctor_933_, 0);
        crate::leanh::lean_inc(v_map_935_);
        crate::leanh::lean_dec_ref(v_toFunctor_933_);
        v___f_936_ = l_Option_mapM___redArg___closed__0;
        v___x_937_ = crate::leanh::lean_apply_1(v_f_928_, v_val_934_);
        v___x_938_ = crate::leanh::lean_apply_4(
            v_map_935_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_936_,
            v___x_937_,
        );
        return v___x_938_;
    }
}
pub unsafe fn l_Option_mapA___redArg(
    mut v_inst_939_: *mut crate::leanh::LeanObject,
    mut v_f_940_: *mut crate::leanh::LeanObject,
    mut v_a_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_941_) == 0 {
        let mut v_toPure_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_940_);
        v_toPure_942_ = crate::leanh::lean_ctor_get(v_inst_939_, 1);
        crate::leanh::lean_inc(v_toPure_942_);
        crate::leanh::lean_dec_ref(v_inst_939_);
        v___x_943_ = crate::leanh::lean_box(0);
        v___x_944_ =
            crate::leanh::lean_apply_2(v_toPure_942_, crate::leanh::lean_box(0), v___x_943_);
        return v___x_944_;
    } else {
        let mut v_toFunctor_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_945_ = crate::leanh::lean_ctor_get(v_inst_939_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_945_);
        crate::leanh::lean_dec_ref(v_inst_939_);
        v_val_946_ = crate::leanh::lean_ctor_get(v_a_941_, 0);
        crate::leanh::lean_inc(v_val_946_);
        crate::leanh::lean_dec_ref_known(v_a_941_, 1);
        v_map_947_ = crate::leanh::lean_ctor_get(v_toFunctor_945_, 0);
        crate::leanh::lean_inc(v_map_947_);
        crate::leanh::lean_dec_ref(v_toFunctor_945_);
        v___f_948_ = l_Option_mapM___redArg___closed__0;
        v___x_949_ = crate::leanh::lean_apply_1(v_f_940_, v_val_946_);
        v___x_950_ = crate::leanh::lean_apply_4(
            v_map_947_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_948_,
            v___x_949_,
        );
        return v___x_950_;
    }
}
pub unsafe fn l_Option_mapA(
    mut v_m_951_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_953_: *mut crate::leanh::LeanObject,
    mut v_inst_954_: *mut crate::leanh::LeanObject,
    mut v_f_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_956_) == 0 {
        let mut v_toPure_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_955_);
        v_toPure_957_ = crate::leanh::lean_ctor_get(v_inst_954_, 1);
        crate::leanh::lean_inc(v_toPure_957_);
        crate::leanh::lean_dec_ref(v_inst_954_);
        v___x_958_ = crate::leanh::lean_box(0);
        v___x_959_ =
            crate::leanh::lean_apply_2(v_toPure_957_, crate::leanh::lean_box(0), v___x_958_);
        return v___x_959_;
    } else {
        let mut v_toFunctor_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_960_ = crate::leanh::lean_ctor_get(v_inst_954_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_960_);
        crate::leanh::lean_dec_ref(v_inst_954_);
        v_val_961_ = crate::leanh::lean_ctor_get(v_a_956_, 0);
        crate::leanh::lean_inc(v_val_961_);
        crate::leanh::lean_dec_ref_known(v_a_956_, 1);
        v_map_962_ = crate::leanh::lean_ctor_get(v_toFunctor_960_, 0);
        crate::leanh::lean_inc(v_map_962_);
        crate::leanh::lean_dec_ref(v_toFunctor_960_);
        v___f_963_ = l_Option_mapM___redArg___closed__0;
        v___x_964_ = crate::leanh::lean_apply_1(v_f_955_, v_val_961_);
        v___x_965_ = crate::leanh::lean_apply_4(
            v_map_962_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_963_,
            v___x_964_,
        );
        return v___x_965_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0(
    mut v_x_966_: *mut crate::leanh::LeanObject,
    mut v_b_967_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_b_967_ == 0 {
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_968_ = crate::leanh::lean_box(0);
        return v___x_968_;
    } else {
        crate::leanh::lean_inc(v_x_966_);
        return v_x_966_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0___boxed(
    mut v_x_969_: *mut crate::leanh::LeanObject,
    mut v_b_970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_971_: u8 = 0;
    let mut v_res_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_971_ = (crate::leanh::lean_unbox(v_b_970_) as u8);
    v_res_972_ = l_Option_filterM___redArg___lam__0(v_x_969_, v_b_boxed_971_);
    crate::leanh::lean_dec(v_x_969_);
    return v_res_972_;
}
pub unsafe fn l_Option_filterM___redArg(
    mut v_inst_973_: *mut crate::leanh::LeanObject,
    mut v_p_974_: *mut crate::leanh::LeanObject,
    mut v_x_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_975_) == 0 {
        let mut v_toPure_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_p_974_);
        v_toPure_976_ = crate::leanh::lean_ctor_get(v_inst_973_, 1);
        crate::leanh::lean_inc(v_toPure_976_);
        crate::leanh::lean_dec_ref(v_inst_973_);
        v___x_977_ = crate::leanh::lean_apply_2(v_toPure_976_, crate::leanh::lean_box(0), v_x_975_);
        return v___x_977_;
    } else {
        let mut v_toFunctor_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_978_ = crate::leanh::lean_ctor_get(v_inst_973_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_978_);
        crate::leanh::lean_dec_ref(v_inst_973_);
        v_val_979_ = crate::leanh::lean_ctor_get(v_x_975_, 0);
        crate::leanh::lean_inc(v_val_979_);
        v_map_980_ = crate::leanh::lean_ctor_get(v_toFunctor_978_, 0);
        crate::leanh::lean_inc(v_map_980_);
        crate::leanh::lean_dec_ref(v_toFunctor_978_);
        v___f_981_ = crate::leanh::lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_981_, 0, v_x_975_);
        v___x_982_ = crate::leanh::lean_apply_1(v_p_974_, v_val_979_);
        v___x_983_ = crate::leanh::lean_apply_4(
            v_map_980_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_981_,
            v___x_982_,
        );
        return v___x_983_;
    }
}
pub unsafe fn l_Option_filterM(
    mut v_m_984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_985_: *mut crate::leanh::LeanObject,
    mut v_inst_986_: *mut crate::leanh::LeanObject,
    mut v_p_987_: *mut crate::leanh::LeanObject,
    mut v_x_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_988_) == 0 {
        let mut v_toPure_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_p_987_);
        v_toPure_989_ = crate::leanh::lean_ctor_get(v_inst_986_, 1);
        crate::leanh::lean_inc(v_toPure_989_);
        crate::leanh::lean_dec_ref(v_inst_986_);
        v___x_990_ = crate::leanh::lean_apply_2(v_toPure_989_, crate::leanh::lean_box(0), v_x_988_);
        return v___x_990_;
    } else {
        let mut v_toFunctor_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_991_ = crate::leanh::lean_ctor_get(v_inst_986_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_991_);
        crate::leanh::lean_dec_ref(v_inst_986_);
        v_val_992_ = crate::leanh::lean_ctor_get(v_x_988_, 0);
        crate::leanh::lean_inc(v_val_992_);
        v_map_993_ = crate::leanh::lean_ctor_get(v_toFunctor_991_, 0);
        crate::leanh::lean_inc(v_map_993_);
        crate::leanh::lean_dec_ref(v_toFunctor_991_);
        v___f_994_ = crate::leanh::lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_994_, 0, v_x_988_);
        v___x_995_ = crate::leanh::lean_apply_1(v_p_987_, v_val_992_);
        v___x_996_ = crate::leanh::lean_apply_4(
            v_map_993_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_994_,
            v___x_995_,
        );
        return v___x_996_;
    }
}
pub unsafe fn l_Option_filter___redArg(
    mut v_p_997_: *mut crate::leanh::LeanObject,
    mut v_x_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_998_) == 0 {
        crate::leanh::lean_dec_ref(v_p_997_);
        return v_x_998_;
    } else {
        let mut v_val_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: u8 = 0;
        v_val_999_ = crate::leanh::lean_ctor_get(v_x_998_, 0);
        crate::leanh::lean_inc(v_val_999_);
        v___x_1000_ = crate::leanh::lean_apply_1(v_p_997_, v_val_999_);
        v___x_1001_ = (crate::leanh::lean_unbox(v___x_1000_) as u8);
        if v___x_1001_ == 0 {
            let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_x_998_, 1);
            v___x_1002_ = crate::leanh::lean_box(0);
            return v___x_1002_;
        } else {
            return v_x_998_;
        }
    }
}
pub unsafe fn l_Option_filter(
    mut v_00_u03b1_1003_: *mut crate::leanh::LeanObject,
    mut v_p_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1005_) == 0 {
        crate::leanh::lean_dec_ref(v_p_1004_);
        return v_x_1005_;
    } else {
        let mut v_val_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_val_1006_ = crate::leanh::lean_ctor_get(v_x_1005_, 0);
        crate::leanh::lean_inc(v_val_1006_);
        v___x_1007_ = crate::leanh::lean_apply_1(v_p_1004_, v_val_1006_);
        v___x_1008_ = (crate::leanh::lean_unbox(v___x_1007_) as u8);
        if v___x_1008_ == 0 {
            let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_x_1005_, 1);
            v___x_1009_ = crate::leanh::lean_box(0);
            return v___x_1009_;
        } else {
            return v_x_1005_;
        }
    }
}
pub unsafe fn l_Option_all___redArg(
    mut v_p_1010_: *mut crate::leanh::LeanObject,
    mut v_x_1011_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1011_) == 0 {
        let mut v___x_1012_: u8 = 0;
        crate::leanh::lean_dec_ref(v_p_1010_);
        v___x_1012_ = 1;
        return v___x_1012_;
    } else {
        let mut v_val_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: u8 = 0;
        v_val_1013_ = crate::leanh::lean_ctor_get(v_x_1011_, 0);
        crate::leanh::lean_inc(v_val_1013_);
        crate::leanh::lean_dec_ref_known(v_x_1011_, 1);
        v___x_1014_ = crate::leanh::lean_apply_1(v_p_1010_, v_val_1013_);
        v___x_1015_ = (crate::leanh::lean_unbox(v___x_1014_) as u8);
        return v___x_1015_;
    }
}
pub unsafe fn l_Option_all___redArg___boxed(
    mut v_p_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: u8 = 0;
    let mut v_r_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Option_all___redArg(v_p_1016_, v_x_1017_);
    v_r_1019_ = crate::leanh::lean_box((v_res_1018_) as usize);
    return v_r_1019_;
}
pub unsafe fn l_Option_all(
    mut v_00_u03b1_1020_: *mut crate::leanh::LeanObject,
    mut v_p_1021_: *mut crate::leanh::LeanObject,
    mut v_x_1022_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1022_) == 0 {
        let mut v___x_1023_: u8 = 0;
        crate::leanh::lean_dec_ref(v_p_1021_);
        v___x_1023_ = 1;
        return v___x_1023_;
    } else {
        let mut v_val_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: u8 = 0;
        v_val_1024_ = crate::leanh::lean_ctor_get(v_x_1022_, 0);
        crate::leanh::lean_inc(v_val_1024_);
        crate::leanh::lean_dec_ref_known(v_x_1022_, 1);
        v___x_1025_ = crate::leanh::lean_apply_1(v_p_1021_, v_val_1024_);
        v___x_1026_ = (crate::leanh::lean_unbox(v___x_1025_) as u8);
        return v___x_1026_;
    }
}
pub unsafe fn l_Option_all___boxed(
    mut v_00_u03b1_1027_: *mut crate::leanh::LeanObject,
    mut v_p_1028_: *mut crate::leanh::LeanObject,
    mut v_x_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1030_: u8 = 0;
    let mut v_r_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Option_all(v_00_u03b1_1027_, v_p_1028_, v_x_1029_);
    v_r_1031_ = crate::leanh::lean_box((v_res_1030_) as usize);
    return v_r_1031_;
}
pub unsafe fn l_Option_any___redArg(
    mut v_p_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1033_) == 0 {
        let mut v___x_1034_: u8 = 0;
        crate::leanh::lean_dec_ref(v_p_1032_);
        v___x_1034_ = 0;
        return v___x_1034_;
    } else {
        let mut v_val_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: u8 = 0;
        v_val_1035_ = crate::leanh::lean_ctor_get(v_x_1033_, 0);
        crate::leanh::lean_inc(v_val_1035_);
        crate::leanh::lean_dec_ref_known(v_x_1033_, 1);
        v___x_1036_ = crate::leanh::lean_apply_1(v_p_1032_, v_val_1035_);
        v___x_1037_ = (crate::leanh::lean_unbox(v___x_1036_) as u8);
        return v___x_1037_;
    }
}
pub unsafe fn l_Option_any___redArg___boxed(
    mut v_p_1038_: *mut crate::leanh::LeanObject,
    mut v_x_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1040_: u8 = 0;
    let mut v_r_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1040_ = l_Option_any___redArg(v_p_1038_, v_x_1039_);
    v_r_1041_ = crate::leanh::lean_box((v_res_1040_) as usize);
    return v_r_1041_;
}
pub unsafe fn l_Option_any(
    mut v_00_u03b1_1042_: *mut crate::leanh::LeanObject,
    mut v_p_1043_: *mut crate::leanh::LeanObject,
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1044_) == 0 {
        let mut v___x_1045_: u8 = 0;
        crate::leanh::lean_dec_ref(v_p_1043_);
        v___x_1045_ = 0;
        return v___x_1045_;
    } else {
        let mut v_val_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: u8 = 0;
        v_val_1046_ = crate::leanh::lean_ctor_get(v_x_1044_, 0);
        crate::leanh::lean_inc(v_val_1046_);
        crate::leanh::lean_dec_ref_known(v_x_1044_, 1);
        v___x_1047_ = crate::leanh::lean_apply_1(v_p_1043_, v_val_1046_);
        v___x_1048_ = (crate::leanh::lean_unbox(v___x_1047_) as u8);
        return v___x_1048_;
    }
}
pub unsafe fn l_Option_any___boxed(
    mut v_00_u03b1_1049_: *mut crate::leanh::LeanObject,
    mut v_p_1050_: *mut crate::leanh::LeanObject,
    mut v_x_1051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1052_: u8 = 0;
    let mut v_r_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1052_ = l_Option_any(v_00_u03b1_1049_, v_p_1050_, v_x_1051_);
    v_r_1053_ = crate::leanh::lean_box((v_res_1052_) as usize);
    return v_r_1053_;
}
pub unsafe fn l_Option_instOrElse___lam__0(
    mut v_x_1054_: *mut crate::leanh::LeanObject,
    mut v_x_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1054_) == 0 {
        let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1056_ = crate::leanh::lean_box(0);
        v___x_1057_ = crate::leanh::lean_apply_1(v_x_1055_, v___x_1056_);
        return v___x_1057_;
    } else {
        crate::leanh::lean_dec_ref(v_x_1055_);
        crate::leanh::lean_inc_ref(v_x_1054_);
        return v_x_1054_;
    }
}
pub unsafe fn l_Option_instOrElse___lam__0___boxed(
    mut v_x_1058_: *mut crate::leanh::LeanObject,
    mut v_x_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Option_instOrElse___lam__0(v_x_1058_, v_x_1059_);
    crate::leanh::lean_dec(v_x_1058_);
    return v_res_1060_;
}
pub unsafe fn l_Option_instOrElse(
    mut v_00_u03b1_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1063_ = l_Option_instOrElse___closed__0;
    return v___f_1063_;
}
pub unsafe fn l_Option_instDecidableRelLt___redArg(
    mut v_s_1064_: *mut crate::leanh::LeanObject,
    mut v_x_1065_: *mut crate::leanh::LeanObject,
    mut v_x_1066_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1065_) == 0 {
        crate::leanh::lean_dec_ref(v_s_1064_);
        if crate::leanh::lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1067_: u8 = 0;
            v___x_1067_ = 0;
            return v___x_1067_;
        } else {
            let mut v___x_1068_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1066_, 1);
            v___x_1068_ = 1;
            return v___x_1068_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1069_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1065_, 1);
            crate::leanh::lean_dec_ref(v_s_1064_);
            v___x_1069_ = 0;
            return v___x_1069_;
        } else {
            let mut v_val_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1073_: u8 = 0;
            v_val_1070_ = crate::leanh::lean_ctor_get(v_x_1065_, 0);
            crate::leanh::lean_inc(v_val_1070_);
            crate::leanh::lean_dec_ref_known(v_x_1065_, 1);
            v_val_1071_ = crate::leanh::lean_ctor_get(v_x_1066_, 0);
            crate::leanh::lean_inc(v_val_1071_);
            crate::leanh::lean_dec_ref_known(v_x_1066_, 1);
            v___x_1072_ = crate::leanh::lean_apply_2(v_s_1064_, v_val_1070_, v_val_1071_);
            v___x_1073_ = (crate::leanh::lean_unbox(v___x_1072_) as u8);
            return v___x_1073_;
        }
    }
}
pub unsafe fn l_Option_instDecidableRelLt___redArg___boxed(
    mut v_s_1074_: *mut crate::leanh::LeanObject,
    mut v_x_1075_: *mut crate::leanh::LeanObject,
    mut v_x_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1077_: u8 = 0;
    let mut v_r_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Option_instDecidableRelLt___redArg(v_s_1074_, v_x_1075_, v_x_1076_);
    v_r_1078_ = crate::leanh::lean_box((v_res_1077_) as usize);
    return v_r_1078_;
}
pub unsafe fn l_Option_instDecidableRelLt(
    mut v_00_u03b1_1079_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1080_: *mut crate::leanh::LeanObject,
    mut v_r_1081_: *mut crate::leanh::LeanObject,
    mut v_s_1082_: *mut crate::leanh::LeanObject,
    mut v_x_1083_: *mut crate::leanh::LeanObject,
    mut v_x_1084_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1085_: u8 = 0;
    v___x_1085_ = l_Option_instDecidableRelLt___redArg(v_s_1082_, v_x_1083_, v_x_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Option_instDecidableRelLt___boxed(
    mut v_00_u03b1_1086_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1087_: *mut crate::leanh::LeanObject,
    mut v_r_1088_: *mut crate::leanh::LeanObject,
    mut v_s_1089_: *mut crate::leanh::LeanObject,
    mut v_x_1090_: *mut crate::leanh::LeanObject,
    mut v_x_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: u8 = 0;
    let mut v_r_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Option_instDecidableRelLt(
        v_00_u03b1_1086_,
        v_00_u03b2_1087_,
        v_r_1088_,
        v_s_1089_,
        v_x_1090_,
        v_x_1091_,
    );
    v_r_1093_ = crate::leanh::lean_box((v_res_1092_) as usize);
    return v_r_1093_;
}
pub unsafe fn l_Option_merge___redArg(
    mut v_fn_1094_: *mut crate::leanh::LeanObject,
    mut v_x_1095_: *mut crate::leanh::LeanObject,
    mut v_x_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1095_) == 0 {
                    crate::leanh::lean_dec(v_fn_1094_);
                    return v_x_1096_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1096_) == 0 {
                        crate::leanh::lean_dec(v_fn_1094_);
                        return v_x_1095_;
                    } else {
                        v_val_1097_ = crate::leanh::lean_ctor_get(v_x_1095_, 0);
                        crate::leanh::lean_inc(v_val_1097_);
                        crate::leanh::lean_dec_ref_known(v_x_1095_, 1);
                        v_val_1098_ = crate::leanh::lean_ctor_get(v_x_1096_, 0);
                        v_isSharedCheck_1106_ = (!crate::leanh::lean_is_exclusive(v_x_1096_)) as u8;
                        if v_isSharedCheck_1106_ == 0 {
                            v___x_1100_ = v_x_1096_;
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1098_);
                            crate::leanh::lean_dec(v_x_1096_);
                            v___x_1100_ = crate::leanh::lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1102_ = crate::leanh::lean_apply_2(v_fn_1094_, v_val_1097_, v_val_1098_);
                if v_isShared_1101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1100_, 0, v___x_1102_);
                    v___x_1104_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_merge(
    mut v_00_u03b1_1107_: *mut crate::leanh::LeanObject,
    mut v_fn_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
    mut v_x_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Option_merge___redArg(v_fn_1108_, v_x_1109_, v_x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Option_elim___redArg(
    mut v_x_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
    mut v_x_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1112_) == 0 {
        crate::leanh::lean_dec(v_x_1114_);
        crate::leanh::lean_inc(v_x_1113_);
        return v_x_1113_;
    } else {
        let mut v_val_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1115_ = crate::leanh::lean_ctor_get(v_x_1112_, 0);
        crate::leanh::lean_inc(v_val_1115_);
        crate::leanh::lean_dec_ref_known(v_x_1112_, 1);
        v___x_1116_ = crate::leanh::lean_apply_1(v_x_1114_, v_val_1115_);
        return v___x_1116_;
    }
}
pub unsafe fn l_Option_elim___redArg___boxed(
    mut v_x_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Option_elim___redArg(v_x_1117_, v_x_1118_, v_x_1119_);
    crate::leanh::lean_dec(v_x_1118_);
    return v_res_1120_;
}
pub unsafe fn l_Option_elim(
    mut v_00_u03b1_1121_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1122_: *mut crate::leanh::LeanObject,
    mut v_x_1123_: *mut crate::leanh::LeanObject,
    mut v_x_1124_: *mut crate::leanh::LeanObject,
    mut v_x_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1123_) == 0 {
        crate::leanh::lean_dec(v_x_1125_);
        crate::leanh::lean_inc(v_x_1124_);
        return v_x_1124_;
    } else {
        let mut v_val_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1126_ = crate::leanh::lean_ctor_get(v_x_1123_, 0);
        crate::leanh::lean_inc(v_val_1126_);
        crate::leanh::lean_dec_ref_known(v_x_1123_, 1);
        v___x_1127_ = crate::leanh::lean_apply_1(v_x_1125_, v_val_1126_);
        return v___x_1127_;
    }
}
pub unsafe fn l_Option_elim___boxed(
    mut v_00_u03b1_1128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
    mut v_x_1131_: *mut crate::leanh::LeanObject,
    mut v_x_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Option_elim(
        v_00_u03b1_1128_,
        v_00_u03b2_1129_,
        v_x_1130_,
        v_x_1131_,
        v_x_1132_,
    );
    crate::leanh::lean_dec(v_x_1131_);
    return v_res_1133_;
}
pub unsafe fn l_Option_get___redArg(
    mut v_x_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_1135_ = crate::leanh::lean_ctor_get(v_x_1134_, 0);
    crate::leanh::lean_inc(v_val_1135_);
    return v_val_1135_;
}
pub unsafe fn l_Option_get___redArg___boxed(
    mut v_x_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Option_get___redArg(v_x_1136_);
    crate::leanh::lean_dec(v_x_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Option_get(
    mut v_00_u03b1_1138_: *mut crate::leanh::LeanObject,
    mut v_x_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_1141_ = crate::leanh::lean_ctor_get(v_x_1139_, 0);
    crate::leanh::lean_inc(v_val_1141_);
    return v_val_1141_;
}
pub unsafe fn l_Option_get___boxed(
    mut v_00_u03b1_1142_: *mut crate::leanh::LeanObject,
    mut v_x_1143_: *mut crate::leanh::LeanObject,
    mut v_x_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Option_get(v_00_u03b1_1142_, v_x_1143_, v_x_1144_);
    crate::leanh::lean_dec(v_x_1143_);
    return v_res_1145_;
}
pub unsafe fn l_Option_guard___redArg(
    mut v_p_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    crate::leanh::lean_inc(v_a_1147_);
    v___x_1148_ = crate::leanh::lean_apply_1(v_p_1146_, v_a_1147_);
    v___x_1149_ = (crate::leanh::lean_unbox(v___x_1148_) as u8);
    if v___x_1149_ == 0 {
        let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1147_);
        v___x_1150_ = crate::leanh::lean_box(0);
        return v___x_1150_;
    } else {
        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1151_, 0, v_a_1147_);
        return v___x_1151_;
    }
}
pub unsafe fn l_Option_guard(
    mut v_00_u03b1_1152_: *mut crate::leanh::LeanObject,
    mut v_p_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    crate::leanh::lean_inc(v_a_1154_);
    v___x_1155_ = crate::leanh::lean_apply_1(v_p_1153_, v_a_1154_);
    v___x_1156_ = (crate::leanh::lean_unbox(v___x_1155_) as u8);
    if v___x_1156_ == 0 {
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1154_);
        v___x_1157_ = crate::leanh::lean_box(0);
        return v___x_1157_;
    } else {
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1158_, 0, v_a_1154_);
        return v___x_1158_;
    }
}
pub unsafe fn l_Option_toList___redArg(
    mut v_x_1159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1159_) == 0 {
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1160_ = crate::leanh::lean_box(0);
        return v___x_1160_;
    } else {
        let mut v_val_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1161_ = crate::leanh::lean_ctor_get(v_x_1159_, 0);
        v___x_1162_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_val_1161_);
        v___x_1163_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1163_, 0, v_val_1161_);
        crate::leanh::lean_ctor_set(v___x_1163_, 1, v___x_1162_);
        return v___x_1163_;
    }
}
pub unsafe fn l_Option_toList___redArg___boxed(
    mut v_x_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Option_toList___redArg(v_x_1164_);
    crate::leanh::lean_dec(v_x_1164_);
    return v_res_1165_;
}
pub unsafe fn l_Option_toList(
    mut v_00_u03b1_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1167_) == 0 {
        let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1168_ = crate::leanh::lean_box(0);
        return v___x_1168_;
    } else {
        let mut v_val_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1169_ = crate::leanh::lean_ctor_get(v_x_1167_, 0);
        v___x_1170_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_val_1169_);
        v___x_1171_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1171_, 0, v_val_1169_);
        crate::leanh::lean_ctor_set(v___x_1171_, 1, v___x_1170_);
        return v___x_1171_;
    }
}
pub unsafe fn l_Option_toList___boxed(
    mut v_00_u03b1_1172_: *mut crate::leanh::LeanObject,
    mut v_x_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1174_ = l_Option_toList(v_00_u03b1_1172_, v_x_1173_);
    crate::leanh::lean_dec(v_x_1173_);
    return v_res_1174_;
}
pub unsafe fn l_Option_toArray___redArg(
    mut v_x_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1177_) == 0 {
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1178_ = l_Option_toArray___redArg___closed__0;
        return v___x_1178_;
    } else {
        let mut v_val_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1179_ = crate::leanh::lean_ctor_get(v_x_1177_, 0);
        crate::leanh::lean_inc(v_val_1179_);
        crate::leanh::lean_dec_ref_known(v_x_1177_, 1);
        v___x_1180_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
        v___x_1182_ = lean_array_push(v___x_1181_, v_val_1179_);
        return v___x_1182_;
    }
}
pub unsafe fn l_Option_toArray(
    mut v_00_u03b1_1183_: *mut crate::leanh::LeanObject,
    mut v_x_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1184_) == 0 {
        let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1185_ = l_Option_toArray___redArg___closed__0;
        return v___x_1185_;
    } else {
        let mut v_val_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1186_ = crate::leanh::lean_ctor_get(v_x_1184_, 0);
        crate::leanh::lean_inc(v_val_1186_);
        crate::leanh::lean_dec_ref_known(v_x_1184_, 1);
        v___x_1187_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1188_ = lean_mk_empty_array_with_capacity(v___x_1187_);
        v___x_1189_ = lean_array_push(v___x_1188_, v_val_1186_);
        return v___x_1189_;
    }
}
pub unsafe fn l_Option_join___redArg(
    mut v_x_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1190_) == 0 {
        let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1191_ = crate::leanh::lean_box(0);
        return v___x_1191_;
    } else {
        let mut v_val_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1192_ = crate::leanh::lean_ctor_get(v_x_1190_, 0);
        crate::leanh::lean_inc(v_val_1192_);
        return v_val_1192_;
    }
}
pub unsafe fn l_Option_join___redArg___boxed(
    mut v_x_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Option_join___redArg(v_x_1193_);
    crate::leanh::lean_dec(v_x_1193_);
    return v_res_1194_;
}
pub unsafe fn l_Option_join(
    mut v_00_u03b1_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1196_) == 0 {
        let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1197_ = crate::leanh::lean_box(0);
        return v___x_1197_;
    } else {
        let mut v_val_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1198_ = crate::leanh::lean_ctor_get(v_x_1196_, 0);
        crate::leanh::lean_inc(v_val_1198_);
        return v_val_1198_;
    }
}
pub unsafe fn l_Option_join___boxed(
    mut v_00_u03b1_1199_: *mut crate::leanh::LeanObject,
    mut v_x_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Option_join(v_00_u03b1_1199_, v_x_1200_);
    crate::leanh::lean_dec(v_x_1200_);
    return v_res_1201_;
}
pub unsafe fn l_Option_sequence___redArg(
    mut v_inst_1202_: *mut crate::leanh::LeanObject,
    mut v_x_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1203_) == 0 {
        let mut v_toPure_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toPure_1204_ = crate::leanh::lean_ctor_get(v_inst_1202_, 1);
        crate::leanh::lean_inc(v_toPure_1204_);
        crate::leanh::lean_dec_ref(v_inst_1202_);
        v___x_1205_ = crate::leanh::lean_box(0);
        v___x_1206_ =
            crate::leanh::lean_apply_2(v_toPure_1204_, crate::leanh::lean_box(0), v___x_1205_);
        return v___x_1206_;
    } else {
        let mut v_toFunctor_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_1207_ = crate::leanh::lean_ctor_get(v_inst_1202_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_1207_);
        crate::leanh::lean_dec_ref(v_inst_1202_);
        v_val_1208_ = crate::leanh::lean_ctor_get(v_x_1203_, 0);
        crate::leanh::lean_inc(v_val_1208_);
        crate::leanh::lean_dec_ref_known(v_x_1203_, 1);
        v_map_1209_ = crate::leanh::lean_ctor_get(v_toFunctor_1207_, 0);
        crate::leanh::lean_inc(v_map_1209_);
        crate::leanh::lean_dec_ref(v_toFunctor_1207_);
        v___f_1210_ = l_Option_mapM___redArg___closed__0;
        v___x_1211_ = crate::leanh::lean_apply_4(
            v_map_1209_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_1210_,
            v_val_1208_,
        );
        return v___x_1211_;
    }
}
pub unsafe fn l_Option_sequence(
    mut v_m_1212_: *mut crate::leanh::LeanObject,
    mut v_inst_1213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1214_: *mut crate::leanh::LeanObject,
    mut v_x_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1215_) == 0 {
        let mut v_toPure_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toPure_1216_ = crate::leanh::lean_ctor_get(v_inst_1213_, 1);
        crate::leanh::lean_inc(v_toPure_1216_);
        crate::leanh::lean_dec_ref(v_inst_1213_);
        v___x_1217_ = crate::leanh::lean_box(0);
        v___x_1218_ =
            crate::leanh::lean_apply_2(v_toPure_1216_, crate::leanh::lean_box(0), v___x_1217_);
        return v___x_1218_;
    } else {
        let mut v_toFunctor_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_1219_ = crate::leanh::lean_ctor_get(v_inst_1213_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_1219_);
        crate::leanh::lean_dec_ref(v_inst_1213_);
        v_val_1220_ = crate::leanh::lean_ctor_get(v_x_1215_, 0);
        crate::leanh::lean_inc(v_val_1220_);
        crate::leanh::lean_dec_ref_known(v_x_1215_, 1);
        v_map_1221_ = crate::leanh::lean_ctor_get(v_toFunctor_1219_, 0);
        crate::leanh::lean_inc(v_map_1221_);
        crate::leanh::lean_dec_ref(v_toFunctor_1219_);
        v___f_1222_ = l_Option_mapM___redArg___closed__0;
        v___x_1223_ = crate::leanh::lean_apply_4(
            v_map_1221_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_1222_,
            v_val_1220_,
        );
        return v___x_1223_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0(
    mut v_y_1224_: *mut crate::leanh::LeanObject,
    mut v_z_1225_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1226_) == 0 {
        crate::leanh::lean_dec(v_z_1225_);
        crate::leanh::lean_inc(v_y_1224_);
        return v_y_1224_;
    } else {
        let mut v_val_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1227_ = crate::leanh::lean_ctor_get(v_____do__lift_1226_, 0);
        crate::leanh::lean_inc(v_val_1227_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1228_ = crate::leanh::lean_apply_1(v_z_1225_, v_val_1227_);
        return v___x_1228_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0___boxed(
    mut v_y_1229_: *mut crate::leanh::LeanObject,
    mut v_z_1230_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Option_elimM___redArg___lam__0(v_y_1229_, v_z_1230_, v_____do__lift_1231_);
    crate::leanh::lean_dec(v_y_1229_);
    return v_res_1232_;
}
pub unsafe fn l_Option_elimM___redArg(
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_x_1234_: *mut crate::leanh::LeanObject,
    mut v_y_1235_: *mut crate::leanh::LeanObject,
    mut v_z_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1237_ = crate::leanh::lean_ctor_get(v_inst_1233_, 1);
    crate::leanh::lean_inc(v_toBind_1237_);
    crate::leanh::lean_dec_ref(v_inst_1233_);
    v___f_1238_ = crate::leanh::lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1238_, 0, v_y_1235_);
    crate::leanh::lean_closure_set(v___f_1238_, 1, v_z_1236_);
    v___x_1239_ = crate::leanh::lean_apply_4(
        v_toBind_1237_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_1234_,
        v___f_1238_,
    );
    return v___x_1239_;
}
pub unsafe fn l_Option_elimM(
    mut v_m_1240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
    mut v_x_1244_: *mut crate::leanh::LeanObject,
    mut v_y_1245_: *mut crate::leanh::LeanObject,
    mut v_z_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1247_ = crate::leanh::lean_ctor_get(v_inst_1243_, 1);
    crate::leanh::lean_inc(v_toBind_1247_);
    crate::leanh::lean_dec_ref(v_inst_1243_);
    v___f_1248_ = crate::leanh::lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1248_, 0, v_y_1245_);
    crate::leanh::lean_closure_set(v___f_1248_, 1, v_z_1246_);
    v___x_1249_ = crate::leanh::lean_apply_4(
        v_toBind_1247_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_1244_,
        v___f_1248_,
    );
    return v___x_1249_;
}
pub unsafe fn l_Option_getDM___redArg(
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
    mut v_x_1251_: *mut crate::leanh::LeanObject,
    mut v_y_1252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1251_) == 0 {
        crate::leanh::lean_dec(v_inst_1250_);
        crate::leanh::lean_inc(v_y_1252_);
        return v_y_1252_;
    } else {
        let mut v_val_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1253_ = crate::leanh::lean_ctor_get(v_x_1251_, 0);
        crate::leanh::lean_inc(v_val_1253_);
        crate::leanh::lean_dec_ref_known(v_x_1251_, 1);
        v___x_1254_ =
            crate::leanh::lean_apply_2(v_inst_1250_, crate::leanh::lean_box(0), v_val_1253_);
        return v___x_1254_;
    }
}
pub unsafe fn l_Option_getDM___redArg___boxed(
    mut v_inst_1255_: *mut crate::leanh::LeanObject,
    mut v_x_1256_: *mut crate::leanh::LeanObject,
    mut v_y_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Option_getDM___redArg(v_inst_1255_, v_x_1256_, v_y_1257_);
    crate::leanh::lean_dec(v_y_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Option_getDM(
    mut v_m_1259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1260_: *mut crate::leanh::LeanObject,
    mut v_inst_1261_: *mut crate::leanh::LeanObject,
    mut v_x_1262_: *mut crate::leanh::LeanObject,
    mut v_y_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1262_) == 0 {
        crate::leanh::lean_dec(v_inst_1261_);
        crate::leanh::lean_inc(v_y_1263_);
        return v_y_1263_;
    } else {
        let mut v_val_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1264_ = crate::leanh::lean_ctor_get(v_x_1262_, 0);
        crate::leanh::lean_inc(v_val_1264_);
        crate::leanh::lean_dec_ref_known(v_x_1262_, 1);
        v___x_1265_ =
            crate::leanh::lean_apply_2(v_inst_1261_, crate::leanh::lean_box(0), v_val_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l_Option_getDM___boxed(
    mut v_m_1266_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1267_: *mut crate::leanh::LeanObject,
    mut v_inst_1268_: *mut crate::leanh::LeanObject,
    mut v_x_1269_: *mut crate::leanh::LeanObject,
    mut v_y_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Option_getDM(
        v_m_1266_,
        v_00_u03b1_1267_,
        v_inst_1268_,
        v_x_1269_,
        v_y_1270_,
    );
    crate::leanh::lean_dec(v_y_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Option_min___redArg(
    mut v_inst_1272_: *mut crate::leanh::LeanObject,
    mut v_x_1273_: *mut crate::leanh::LeanObject,
    mut v_x_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1273_) == 0 {
                    crate::leanh::lean_dec(v_inst_1272_);
                    if crate::leanh::lean_obj_tag(v_x_1274_) == 0 {
                        return v_x_1274_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_1274_, 1);
                        return v_x_1273_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1274_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_1273_, 1);
                        crate::leanh::lean_dec(v_inst_1272_);
                        return v_x_1274_;
                    } else {
                        v_val_1275_ = crate::leanh::lean_ctor_get(v_x_1273_, 0);
                        crate::leanh::lean_inc(v_val_1275_);
                        crate::leanh::lean_dec_ref_known(v_x_1273_, 1);
                        v_val_1276_ = crate::leanh::lean_ctor_get(v_x_1274_, 0);
                        v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v_x_1274_)) as u8;
                        if v_isSharedCheck_1284_ == 0 {
                            v___x_1278_ = v_x_1274_;
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1276_);
                            crate::leanh::lean_dec(v_x_1274_);
                            v___x_1278_ = crate::leanh::lean_box(0);
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1280_ = crate::leanh::lean_apply_2(v_inst_1272_, v_val_1275_, v_val_1276_);
                if v_isShared_1279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1280_);
                    v___x_1282_ = v___x_1278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
                    v___x_1282_ = v_reuseFailAlloc_1283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_min(
    mut v_00_u03b1_1285_: *mut crate::leanh::LeanObject,
    mut v_inst_1286_: *mut crate::leanh::LeanObject,
    mut v_x_1287_: *mut crate::leanh::LeanObject,
    mut v_x_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = l_Option_min___redArg(v_inst_1286_, v_x_1287_, v_x_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Option_instMin___redArg(
    mut v_inst_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = crate::leanh::lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1291_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1291_, 1, v_inst_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Option_instMin(
    mut v_00_u03b1_1292_: *mut crate::leanh::LeanObject,
    mut v_inst_1293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = crate::leanh::lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1294_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1294_, 1, v_inst_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Option_max___redArg(
    mut v_inst_1295_: *mut crate::leanh::LeanObject,
    mut v_x_1296_: *mut crate::leanh::LeanObject,
    mut v_x_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1296_) == 0 {
                    crate::leanh::lean_dec(v_inst_1295_);
                    return v_x_1297_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1297_) == 0 {
                        crate::leanh::lean_dec(v_inst_1295_);
                        return v_x_1296_;
                    } else {
                        v_val_1298_ = crate::leanh::lean_ctor_get(v_x_1296_, 0);
                        crate::leanh::lean_inc(v_val_1298_);
                        crate::leanh::lean_dec_ref_known(v_x_1296_, 1);
                        v_val_1299_ = crate::leanh::lean_ctor_get(v_x_1297_, 0);
                        v_isSharedCheck_1307_ = (!crate::leanh::lean_is_exclusive(v_x_1297_)) as u8;
                        if v_isSharedCheck_1307_ == 0 {
                            v___x_1301_ = v_x_1297_;
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1299_);
                            crate::leanh::lean_dec(v_x_1297_);
                            v___x_1301_ = crate::leanh::lean_box(0);
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1303_ = crate::leanh::lean_apply_2(v_inst_1295_, v_val_1298_, v_val_1299_);
                if v_isShared_1302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1303_);
                    v___x_1305_ = v___x_1301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
                    v___x_1305_ = v_reuseFailAlloc_1306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_max(
    mut v_00_u03b1_1308_: *mut crate::leanh::LeanObject,
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Option_max___redArg(v_inst_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Option_instMax___redArg(
    mut v_inst_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = crate::leanh::lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1314_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1314_, 1, v_inst_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Option_instMax(
    mut v_00_u03b1_1315_: *mut crate::leanh::LeanObject,
    mut v_inst_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = crate::leanh::lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1317_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1317_, 1, v_inst_1316_);
    return v___x_1317_;
}
pub unsafe fn l_instLTOption(
    mut v_00_u03b1_1318_: *mut crate::leanh::LeanObject,
    mut v_inst_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = crate::leanh::lean_box(0);
    return v___x_1320_;
}
pub unsafe fn l_instLEOption(
    mut v_00_u03b1_1321_: *mut crate::leanh::LeanObject,
    mut v_inst_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = crate::leanh::lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_instFunctorOption___lam__0(
    mut v_00_u03b1_1324_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v_unused_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_1327_) == 0 {
                    crate::leanh::lean_dec(v___y_1326_);
                    v___x_1328_ = crate::leanh::lean_box(0);
                    return v___x_1328_;
                } else {
                    v_isSharedCheck_1335_ = (!crate::leanh::lean_is_exclusive(v___y_1327_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v_unused_1336_ = crate::leanh::lean_ctor_get(v___y_1327_, 0);
                        crate::leanh::lean_dec(v_unused_1336_);
                        v___x_1330_ = v___y_1327_;
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_1327_);
                        v___x_1330_ = crate::leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1330_, 0, v___y_1326_);
                    v___x_1333_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___y_1326_);
                    v___x_1333_ = v_reuseFailAlloc_1334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadOption___lam__0(
    mut v_00_u03b1_1343_: *mut crate::leanh::LeanObject,
    mut v___y_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1345_, 0, v___y_1344_);
    return v___x_1345_;
}
pub unsafe fn l_instMonadOption___lam__1(
    mut v_00_u03b1_1346_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1347_: *mut crate::leanh::LeanObject,
    mut v_f_1348_: *mut crate::leanh::LeanObject,
    mut v_x_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_f_1348_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_1349_);
                    v___x_1350_ = crate::leanh::lean_box(0);
                    return v___x_1350_;
                } else {
                    v_val_1351_ = crate::leanh::lean_ctor_get(v_f_1348_, 0);
                    crate::leanh::lean_inc(v_val_1351_);
                    crate::leanh::lean_dec_ref_known(v_f_1348_, 1);
                    v___x_1352_ = crate::leanh::lean_box(0);
                    v___x_1353_ = crate::leanh::lean_apply_1(v_x_1349_, v___x_1352_);
                    if crate::leanh::lean_obj_tag(v___x_1353_) == 0 {
                        crate::leanh::lean_dec(v_val_1351_);
                        v___x_1354_ = crate::leanh::lean_box(0);
                        return v___x_1354_;
                    } else {
                        v_val_1355_ = crate::leanh::lean_ctor_get(v___x_1353_, 0);
                        v_isSharedCheck_1363_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1353_)) as u8;
                        if v_isSharedCheck_1363_ == 0 {
                            v___x_1357_ = v___x_1353_;
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1355_);
                            crate::leanh::lean_dec(v___x_1353_);
                            v___x_1357_ = crate::leanh::lean_box(0);
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1359_ = crate::leanh::lean_apply_1(v_val_1351_, v_val_1355_);
                if v_isShared_1358_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1359_);
                    v___x_1361_ = v___x_1357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instMonadOption___lam__2(
    mut v_00_u03b1_1364_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1365_: *mut crate::leanh::LeanObject,
    mut v_x_1366_: *mut crate::leanh::LeanObject,
    mut v_y_1367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1366_) == 0 {
        crate::leanh::lean_dec_ref(v_y_1367_);
        return v_x_1366_;
    } else {
        let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1368_ = crate::leanh::lean_box(0);
        v___x_1369_ = crate::leanh::lean_apply_1(v_y_1367_, v___x_1368_);
        if crate::leanh::lean_obj_tag(v___x_1369_) == 0 {
            let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1370_ = crate::leanh::lean_box(0);
            return v___x_1370_;
        } else {
            crate::leanh::lean_dec_ref_known(v___x_1369_, 1);
            crate::leanh::lean_inc_ref(v_x_1366_);
            return v_x_1366_;
        }
    }
}
pub unsafe fn l_instMonadOption___lam__2___boxed(
    mut v_00_u03b1_1371_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut crate::leanh::LeanObject,
    mut v_x_1373_: *mut crate::leanh::LeanObject,
    mut v_y_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_instMonadOption___lam__2(v_00_u03b1_1371_, v_00_u03b2_1372_, v_x_1373_, v_y_1374_);
    crate::leanh::lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_instMonadOption___lam__3(
    mut v_00_u03b1_1376_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
    mut v_y_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1378_) == 0 {
        let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_y_1379_);
        v___x_1380_ = crate::leanh::lean_box(0);
        return v___x_1380_;
    } else {
        let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1381_ = crate::leanh::lean_box(0);
        v___x_1382_ = crate::leanh::lean_apply_1(v_y_1379_, v___x_1381_);
        return v___x_1382_;
    }
}
pub unsafe fn l_instMonadOption___lam__3___boxed(
    mut v_00_u03b1_1383_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1384_: *mut crate::leanh::LeanObject,
    mut v_x_1385_: *mut crate::leanh::LeanObject,
    mut v_y_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ =
        l_instMonadOption___lam__3(v_00_u03b1_1383_, v_00_u03b2_1384_, v_x_1385_, v_y_1386_);
    crate::leanh::lean_dec(v_x_1385_);
    return v_res_1387_;
}
pub unsafe fn l_instAlternativeOption___lam__0(
    mut v_00_u03b1_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = crate::leanh::lean_box(0);
    return v___x_1404_;
}
pub unsafe fn l_instAlternativeOption___lam__1(
    mut v_00_u03b1_1405_: *mut crate::leanh::LeanObject,
    mut v_x_1406_: *mut crate::leanh::LeanObject,
    mut v_x_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1406_) == 0 {
        let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1408_ = crate::leanh::lean_box(0);
        v___x_1409_ = crate::leanh::lean_apply_1(v_x_1407_, v___x_1408_);
        return v___x_1409_;
    } else {
        crate::leanh::lean_dec_ref(v_x_1407_);
        crate::leanh::lean_inc_ref(v_x_1406_);
        return v_x_1406_;
    }
}
pub unsafe fn l_instAlternativeOption___lam__1___boxed(
    mut v_00_u03b1_1410_: *mut crate::leanh::LeanObject,
    mut v_x_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_instAlternativeOption___lam__1(v_00_u03b1_1410_, v_x_1411_, v_x_1412_);
    crate::leanh::lean_dec(v_x_1411_);
    return v_res_1413_;
}
pub unsafe fn l_liftOption___redArg(
    mut v_inst_1421_: *mut crate::leanh::LeanObject,
    mut v_x_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1422_) == 0 {
        let mut v_failure_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_failure_1423_ = crate::leanh::lean_ctor_get(v_inst_1421_, 1);
        crate::leanh::lean_inc(v_failure_1423_);
        crate::leanh::lean_dec_ref(v_inst_1421_);
        v___x_1424_ = crate::leanh::lean_apply_1(v_failure_1423_, crate::leanh::lean_box(0));
        return v___x_1424_;
    } else {
        let mut v_toApplicative_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1425_ = crate::leanh::lean_ctor_get(v_inst_1421_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1425_);
        crate::leanh::lean_dec_ref(v_inst_1421_);
        v_toPure_1426_ = crate::leanh::lean_ctor_get(v_toApplicative_1425_, 1);
        crate::leanh::lean_inc(v_toPure_1426_);
        crate::leanh::lean_dec_ref(v_toApplicative_1425_);
        v_val_1427_ = crate::leanh::lean_ctor_get(v_x_1422_, 0);
        crate::leanh::lean_inc(v_val_1427_);
        crate::leanh::lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ =
            crate::leanh::lean_apply_2(v_toPure_1426_, crate::leanh::lean_box(0), v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l_liftOption(
    mut v_m_1429_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1430_: *mut crate::leanh::LeanObject,
    mut v_inst_1431_: *mut crate::leanh::LeanObject,
    mut v_x_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_liftOption___redArg(v_inst_1431_, v_x_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Option_tryCatch___redArg(
    mut v_x_1434_: *mut crate::leanh::LeanObject,
    mut v_handle_1435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1434_) == 0 {
        let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1436_ = crate::leanh::lean_box(0);
        v___x_1437_ = crate::leanh::lean_apply_1(v_handle_1435_, v___x_1436_);
        return v___x_1437_;
    } else {
        crate::leanh::lean_dec_ref(v_handle_1435_);
        crate::leanh::lean_inc_ref(v_x_1434_);
        return v_x_1434_;
    }
}
pub unsafe fn l_Option_tryCatch___redArg___boxed(
    mut v_x_1438_: *mut crate::leanh::LeanObject,
    mut v_handle_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Option_tryCatch___redArg(v_x_1438_, v_handle_1439_);
    crate::leanh::lean_dec(v_x_1438_);
    return v_res_1440_;
}
pub unsafe fn l_Option_tryCatch(
    mut v_00_u03b1_1441_: *mut crate::leanh::LeanObject,
    mut v_x_1442_: *mut crate::leanh::LeanObject,
    mut v_handle_1443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1442_) == 0 {
        let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1444_ = crate::leanh::lean_box(0);
        v___x_1445_ = crate::leanh::lean_apply_1(v_handle_1443_, v___x_1444_);
        return v___x_1445_;
    } else {
        crate::leanh::lean_dec_ref(v_handle_1443_);
        crate::leanh::lean_inc_ref(v_x_1442_);
        return v_x_1442_;
    }
}
pub unsafe fn l_Option_tryCatch___boxed(
    mut v_00_u03b1_1446_: *mut crate::leanh::LeanObject,
    mut v_x_1447_: *mut crate::leanh::LeanObject,
    mut v_handle_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Option_tryCatch(v_00_u03b1_1446_, v_x_1447_, v_handle_1448_);
    crate::leanh::lean_dec(v_x_1447_);
    return v_res_1449_;
}
pub unsafe fn l_instMonadExceptOfUnitOption___lam__0(
    mut v_00_u03b1_1450_: *mut crate::leanh::LeanObject,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = crate::leanh::lean_box(0);
    return v___x_1452_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Basic(builtin);
}
