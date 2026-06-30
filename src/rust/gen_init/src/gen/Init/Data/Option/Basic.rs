// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: Init.Control.Basic Init.Grind.Tactics
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::r#gen::Init::Control::Basic::{
    initialize_Init_Control_Basic, runtime_initialize_Init_Control_Basic,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Prelude::l_Option_map;
pub static l_Option_mapM___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_mapM___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Option_mapM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_mapM___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_instOrElse___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_instOrElse___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Option_instOrElse___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_instOrElse___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_toArray___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Option_toArray___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_toArray___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instFunctorOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instFunctorOption___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFunctorOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__0_value) as *mut leanh::LeanObject;
pub static l_instFunctorOption___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_map as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instFunctorOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__1_value) as *mut leanh::LeanObject;
pub static l_instFunctorOption___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instFunctorOption___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instFunctorOption___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instFunctorOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut leanh::LeanObject;
pub static mut l_instFunctorOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instFunctorOption___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__0_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__1_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadOption___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__3_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__4_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_instFunctorOption___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadOption___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__4_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_bind as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadOption___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__5_value) as *mut leanh::LeanObject;
pub static l_instMonadOption___closed__6_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadOption___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadOption___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut leanh::LeanObject;
pub static mut l_instMonadOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadOption___closed__6_value) as *mut leanh::LeanObject;
pub static l_instAlternativeOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instAlternativeOption___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAlternativeOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__0_value) as *mut leanh::LeanObject;
pub static l_instAlternativeOption___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instAlternativeOption___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAlternativeOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__1_value) as *mut leanh::LeanObject;
pub static l_instAlternativeOption___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instMonadOption___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instAlternativeOption___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instAlternativeOption___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instAlternativeOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut leanh::LeanObject;
pub static mut l_instAlternativeOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAlternativeOption___closed__2_value) as *mut leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadExceptOfUnitOption___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Option_tryCatch___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadExceptOfUnitOption___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instMonadExceptOfUnitOption___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadExceptOfUnitOption___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_instMonadExceptOfUnitOption: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadExceptOfUnitOption___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Option_instDecidableEq___redArg(
    mut v_inst_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_b_732_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_a_731_) == 0 {
        leanh::lean_dec_ref(v_inst_730_);
        if leanh::lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_733_: u8 = 0;
            v___x_733_ = 1;
            return v___x_733_;
        } else {
            let mut v___x_734_: u8 = 0;
            leanh::lean_dec_ref_known(v_b_732_, 1);
            v___x_734_ = 0;
            return v___x_734_;
        }
    } else {
        if leanh::lean_obj_tag(v_b_732_) == 0 {
            let mut v___x_735_: u8 = 0;
            leanh::lean_dec_ref_known(v_a_731_, 1);
            leanh::lean_dec_ref(v_inst_730_);
            v___x_735_ = 0;
            return v___x_735_;
        } else {
            let mut v_val_736_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_737_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_739_: u8 = 0;
            v_val_736_ = leanh::lean_ctor_get(v_a_731_, 0);
            leanh::lean_inc(v_val_736_);
            leanh::lean_dec_ref_known(v_a_731_, 1);
            v_val_737_ = leanh::lean_ctor_get(v_b_732_, 0);
            leanh::lean_inc(v_val_737_);
            leanh::lean_dec_ref_known(v_b_732_, 1);
            v___x_738_ = leanh::lean_apply_2(v_inst_730_, v_val_736_, v_val_737_);
            v___x_739_ = (leanh::lean_unbox(v___x_738_) as u8);
            return v___x_739_;
        }
    }
}
pub unsafe fn l_Option_instDecidableEq___redArg___boxed(
    mut v_inst_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_b_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_743_: u8 = 0;
    let mut v_r_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_743_ = l_Option_instDecidableEq___redArg(v_inst_740_, v_a_741_, v_b_742_);
    v_r_744_ = leanh::lean_box((v_res_743_) as usize);
    return v_r_744_;
}
pub unsafe fn l_Option_instDecidableEq(
    mut v_00_u03b1_745_: *mut leanh::LeanObject,
    mut v_inst_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_b_748_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_749_: u8 = 0;
    v___x_749_ = l_Option_instDecidableEq___redArg(v_inst_746_, v_a_747_, v_b_748_);
    return v___x_749_;
}
pub unsafe fn l_Option_instDecidableEq___boxed(
    mut v_00_u03b1_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
    mut v_a_752_: *mut leanh::LeanObject,
    mut v_b_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_754_: u8 = 0;
    let mut v_r_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Option_instDecidableEq(v_00_u03b1_750_, v_inst_751_, v_a_752_, v_b_753_);
    v_r_755_ = leanh::lean_box((v_res_754_) as usize);
    return v_r_755_;
}
pub unsafe fn l_Option_decidableEqNone___redArg(mut v_o_756_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_o_756_) == 0 {
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
    mut v_o_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Option_decidableEqNone___redArg(v_o_759_);
    leanh::lean_dec(v_o_759_);
    v_r_761_ = leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_Option_decidableEqNone(
    mut v_00_u03b1_762_: *mut leanh::LeanObject,
    mut v_o_763_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_764_: u8 = 0;
    v___x_764_ = l_Option_decidableEqNone___redArg(v_o_763_);
    return v___x_764_;
}
pub unsafe fn l_Option_decidableEqNone___boxed(
    mut v_00_u03b1_765_: *mut leanh::LeanObject,
    mut v_o_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: u8 = 0;
    let mut v_r_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Option_decidableEqNone(v_00_u03b1_765_, v_o_766_);
    leanh::lean_dec(v_o_766_);
    v_r_768_ = leanh::lean_box((v_res_767_) as usize);
    return v_r_768_;
}
pub unsafe fn l_Option_decidableNoneEq___redArg(mut v_o_769_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_o_769_) == 0 {
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
    mut v_o_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_773_: u8 = 0;
    let mut v_r_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Option_decidableNoneEq___redArg(v_o_772_);
    leanh::lean_dec(v_o_772_);
    v_r_774_ = leanh::lean_box((v_res_773_) as usize);
    return v_r_774_;
}
pub unsafe fn l_Option_decidableNoneEq(
    mut v_00_u03b1_775_: *mut leanh::LeanObject,
    mut v_o_776_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_777_: u8 = 0;
    v___x_777_ = l_Option_decidableNoneEq___redArg(v_o_776_);
    return v___x_777_;
}
pub unsafe fn l_Option_decidableNoneEq___boxed(
    mut v_00_u03b1_778_: *mut leanh::LeanObject,
    mut v_o_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Option_decidableNoneEq(v_00_u03b1_778_, v_o_779_);
    leanh::lean_dec(v_o_779_);
    v_r_781_ = leanh::lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn l_Option_instBEq_beq___redArg(
    mut v_inst_782_: *mut leanh::LeanObject,
    mut v_x_783_: *mut leanh::LeanObject,
    mut v_x_784_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_783_) == 0 {
        leanh::lean_dec_ref(v_inst_782_);
        if leanh::lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_785_: u8 = 0;
            v___x_785_ = 1;
            return v___x_785_;
        } else {
            let mut v___x_786_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_784_, 1);
            v___x_786_ = 0;
            return v___x_786_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_784_) == 0 {
            let mut v___x_787_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_783_, 1);
            leanh::lean_dec_ref(v_inst_782_);
            v___x_787_ = 0;
            return v___x_787_;
        } else {
            let mut v_val_788_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_789_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_791_: u8 = 0;
            v_val_788_ = leanh::lean_ctor_get(v_x_783_, 0);
            leanh::lean_inc(v_val_788_);
            leanh::lean_dec_ref_known(v_x_783_, 1);
            v_val_789_ = leanh::lean_ctor_get(v_x_784_, 0);
            leanh::lean_inc(v_val_789_);
            leanh::lean_dec_ref_known(v_x_784_, 1);
            v___x_790_ = leanh::lean_apply_2(v_inst_782_, v_val_788_, v_val_789_);
            v___x_791_ = (leanh::lean_unbox(v___x_790_) as u8);
            return v___x_791_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___redArg___boxed(
    mut v_inst_792_: *mut leanh::LeanObject,
    mut v_x_793_: *mut leanh::LeanObject,
    mut v_x_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_795_: u8 = 0;
    let mut v_r_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Option_instBEq_beq___redArg(v_inst_792_, v_x_793_, v_x_794_);
    v_r_796_ = leanh::lean_box((v_res_795_) as usize);
    return v_r_796_;
}
pub unsafe fn l_Option_instBEq_beq(
    mut v_00_u03b1_797_: *mut leanh::LeanObject,
    mut v_inst_798_: *mut leanh::LeanObject,
    mut v_x_799_: *mut leanh::LeanObject,
    mut v_x_800_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_801_: u8 = 0;
    v___x_801_ = l_Option_instBEq_beq___redArg(v_inst_798_, v_x_799_, v_x_800_);
    return v___x_801_;
}
pub unsafe fn l_Option_instBEq_beq___boxed(
    mut v_00_u03b1_802_: *mut leanh::LeanObject,
    mut v_inst_803_: *mut leanh::LeanObject,
    mut v_x_804_: *mut leanh::LeanObject,
    mut v_x_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Option_instBEq_beq(v_00_u03b1_802_, v_inst_803_, v_x_804_, v_x_805_);
    v_r_807_ = leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Option_instBEq___redArg(
    mut v_inst_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = leanh::lean_alloc_closure(
        l_Option_instBEq_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_809_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_809_, 1, v_inst_808_);
    return v___x_809_;
}
pub unsafe fn l_Option_instBEq(
    mut v_00_u03b1_810_: *mut leanh::LeanObject,
    mut v_inst_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = leanh::lean_alloc_closure(
        l_Option_instBEq_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_812_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_812_, 1, v_inst_811_);
    return v___x_812_;
}
pub unsafe fn l_Option_getM___redArg(
    mut v_inst_813_: *mut leanh::LeanObject,
    mut v_x_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_814_) == 0 {
        let mut v_failure_815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_failure_815_ = leanh::lean_ctor_get(v_inst_813_, 1);
        leanh::lean_inc(v_failure_815_);
        leanh::lean_dec_ref(v_inst_813_);
        v___x_816_ = leanh::lean_apply_1(v_failure_815_, leanh::lean_box(0));
        return v___x_816_;
    } else {
        let mut v_toApplicative_817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_819_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_817_ = leanh::lean_ctor_get(v_inst_813_, 0);
        leanh::lean_inc_ref(v_toApplicative_817_);
        leanh::lean_dec_ref(v_inst_813_);
        v_toPure_818_ = leanh::lean_ctor_get(v_toApplicative_817_, 1);
        leanh::lean_inc(v_toPure_818_);
        leanh::lean_dec_ref(v_toApplicative_817_);
        v_val_819_ = leanh::lean_ctor_get(v_x_814_, 0);
        leanh::lean_inc(v_val_819_);
        leanh::lean_dec_ref_known(v_x_814_, 1);
        v___x_820_ =
            leanh::lean_apply_2(v_toPure_818_, leanh::lean_box(0), v_val_819_);
        return v___x_820_;
    }
}
pub unsafe fn l_Option_getM(
    mut v_m_821_: *mut leanh::LeanObject,
    mut v_00_u03b1_822_: *mut leanh::LeanObject,
    mut v_inst_823_: *mut leanh::LeanObject,
    mut v_x_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = l_Option_getM___redArg(v_inst_823_, v_x_824_);
    return v___x_825_;
}
pub unsafe fn l_Option_isSome___redArg(mut v_x_826_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_826_) == 0 {
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
    mut v_x_829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_830_: u8 = 0;
    let mut v_r_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Option_isSome___redArg(v_x_829_);
    leanh::lean_dec(v_x_829_);
    v_r_831_ = leanh::lean_box((v_res_830_) as usize);
    return v_r_831_;
}
pub unsafe fn l_Option_isSome(
    mut v_00_u03b1_832_: *mut leanh::LeanObject,
    mut v_x_833_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_833_) == 0 {
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
    mut v_00_u03b1_836_: *mut leanh::LeanObject,
    mut v_x_837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_838_: u8 = 0;
    let mut v_r_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_838_ = l_Option_isSome(v_00_u03b1_836_, v_x_837_);
    leanh::lean_dec(v_x_837_);
    v_r_839_ = leanh::lean_box((v_res_838_) as usize);
    return v_r_839_;
}
pub unsafe fn l_Option_isNone___redArg(mut v_x_840_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_840_) == 0 {
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
    mut v_x_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_844_: u8 = 0;
    let mut v_r_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Option_isNone___redArg(v_x_843_);
    leanh::lean_dec(v_x_843_);
    v_r_845_ = leanh::lean_box((v_res_844_) as usize);
    return v_r_845_;
}
pub unsafe fn l_Option_isNone(
    mut v_00_u03b1_846_: *mut leanh::LeanObject,
    mut v_x_847_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_847_) == 0 {
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
    mut v_00_u03b1_850_: *mut leanh::LeanObject,
    mut v_x_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: u8 = 0;
    let mut v_r_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Option_isNone(v_00_u03b1_850_, v_x_851_);
    leanh::lean_dec(v_x_851_);
    v_r_853_ = leanh::lean_box((v_res_852_) as usize);
    return v_r_853_;
}
pub unsafe fn l_Option_isEqSome___redArg(
    mut v_inst_854_: *mut leanh::LeanObject,
    mut v_x_855_: *mut leanh::LeanObject,
    mut v_x_856_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_855_) == 0 {
        let mut v___x_857_: u8 = 0;
        leanh::lean_dec(v_x_856_);
        leanh::lean_dec_ref(v_inst_854_);
        v___x_857_ = 0;
        return v___x_857_;
    } else {
        let mut v_val_858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: u8 = 0;
        v_val_858_ = leanh::lean_ctor_get(v_x_855_, 0);
        leanh::lean_inc(v_val_858_);
        leanh::lean_dec_ref_known(v_x_855_, 1);
        v___x_859_ = leanh::lean_apply_2(v_inst_854_, v_val_858_, v_x_856_);
        v___x_860_ = (leanh::lean_unbox(v___x_859_) as u8);
        return v___x_860_;
    }
}
pub unsafe fn l_Option_isEqSome___redArg___boxed(
    mut v_inst_861_: *mut leanh::LeanObject,
    mut v_x_862_: *mut leanh::LeanObject,
    mut v_x_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_864_: u8 = 0;
    let mut v_r_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Option_isEqSome___redArg(v_inst_861_, v_x_862_, v_x_863_);
    v_r_865_ = leanh::lean_box((v_res_864_) as usize);
    return v_r_865_;
}
pub unsafe fn l_Option_isEqSome(
    mut v_00_u03b1_866_: *mut leanh::LeanObject,
    mut v_inst_867_: *mut leanh::LeanObject,
    mut v_x_868_: *mut leanh::LeanObject,
    mut v_x_869_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_868_) == 0 {
        let mut v___x_870_: u8 = 0;
        leanh::lean_dec(v_x_869_);
        leanh::lean_dec_ref(v_inst_867_);
        v___x_870_ = 0;
        return v___x_870_;
    } else {
        let mut v_val_871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: u8 = 0;
        v_val_871_ = leanh::lean_ctor_get(v_x_868_, 0);
        leanh::lean_inc(v_val_871_);
        leanh::lean_dec_ref_known(v_x_868_, 1);
        v___x_872_ = leanh::lean_apply_2(v_inst_867_, v_val_871_, v_x_869_);
        v___x_873_ = (leanh::lean_unbox(v___x_872_) as u8);
        return v___x_873_;
    }
}
pub unsafe fn l_Option_isEqSome___boxed(
    mut v_00_u03b1_874_: *mut leanh::LeanObject,
    mut v_inst_875_: *mut leanh::LeanObject,
    mut v_x_876_: *mut leanh::LeanObject,
    mut v_x_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_878_: u8 = 0;
    let mut v_r_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_878_ = l_Option_isEqSome(v_00_u03b1_874_, v_inst_875_, v_x_876_, v_x_877_);
    v_r_879_ = leanh::lean_box((v_res_878_) as usize);
    return v_r_879_;
}
pub unsafe fn l_Option_bind___redArg(
    mut v_x_880_: *mut leanh::LeanObject,
    mut v_x_881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_880_) == 0 {
        let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_881_);
        v___x_882_ = leanh::lean_box(0);
        return v___x_882_;
    } else {
        let mut v_val_883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_883_ = leanh::lean_ctor_get(v_x_880_, 0);
        leanh::lean_inc(v_val_883_);
        leanh::lean_dec_ref_known(v_x_880_, 1);
        v___x_884_ = leanh::lean_apply_1(v_x_881_, v_val_883_);
        return v___x_884_;
    }
}
pub unsafe fn l_Option_bind(
    mut v_00_u03b1_885_: *mut leanh::LeanObject,
    mut v_00_u03b2_886_: *mut leanh::LeanObject,
    mut v_x_887_: *mut leanh::LeanObject,
    mut v_x_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_887_) == 0 {
        let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_x_888_);
        v___x_889_ = leanh::lean_box(0);
        return v___x_889_;
    } else {
        let mut v_val_890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_890_ = leanh::lean_ctor_get(v_x_887_, 0);
        leanh::lean_inc(v_val_890_);
        leanh::lean_dec_ref_known(v_x_887_, 1);
        v___x_891_ = leanh::lean_apply_1(v_x_888_, v_val_890_);
        return v___x_891_;
    }
}
pub unsafe fn l_Option_bindM___redArg(
    mut v_inst_892_: *mut leanh::LeanObject,
    mut v_f_893_: *mut leanh::LeanObject,
    mut v_x_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_894_) == 0 {
        let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_893_);
        v___x_895_ = leanh::lean_box(0);
        v___x_896_ = leanh::lean_apply_2(v_inst_892_, leanh::lean_box(0), v___x_895_);
        return v___x_896_;
    } else {
        let mut v_val_897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_892_);
        v_val_897_ = leanh::lean_ctor_get(v_x_894_, 0);
        leanh::lean_inc(v_val_897_);
        leanh::lean_dec_ref_known(v_x_894_, 1);
        v___x_898_ = leanh::lean_apply_1(v_f_893_, v_val_897_);
        return v___x_898_;
    }
}
pub unsafe fn l_Option_bindM(
    mut v_m_899_: *mut leanh::LeanObject,
    mut v_00_u03b1_900_: *mut leanh::LeanObject,
    mut v_00_u03b2_901_: *mut leanh::LeanObject,
    mut v_inst_902_: *mut leanh::LeanObject,
    mut v_f_903_: *mut leanh::LeanObject,
    mut v_x_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_904_) == 0 {
        let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_903_);
        v___x_905_ = leanh::lean_box(0);
        v___x_906_ = leanh::lean_apply_2(v_inst_902_, leanh::lean_box(0), v___x_905_);
        return v___x_906_;
    } else {
        let mut v_val_907_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_902_);
        v_val_907_ = leanh::lean_ctor_get(v_x_904_, 0);
        leanh::lean_inc(v_val_907_);
        leanh::lean_dec_ref_known(v_x_904_, 1);
        v___x_908_ = leanh::lean_apply_1(v_f_903_, v_val_907_);
        return v___x_908_;
    }
}
pub unsafe fn l_Option_mapM___redArg___lam__0(
    mut v_val_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_910_, 0, v_val_909_);
    return v___x_910_;
}
pub unsafe fn l_Option_mapM___redArg(
    mut v_inst_912_: *mut leanh::LeanObject,
    mut v_f_913_: *mut leanh::LeanObject,
    mut v_x_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_914_) == 0 {
        let mut v_toPure_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_913_);
        v_toPure_915_ = leanh::lean_ctor_get(v_inst_912_, 1);
        leanh::lean_inc(v_toPure_915_);
        leanh::lean_dec_ref(v_inst_912_);
        v___x_916_ = leanh::lean_box(0);
        v___x_917_ =
            leanh::lean_apply_2(v_toPure_915_, leanh::lean_box(0), v___x_916_);
        return v___x_917_;
    } else {
        let mut v_toFunctor_918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_921_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_918_ = leanh::lean_ctor_get(v_inst_912_, 0);
        leanh::lean_inc_ref(v_toFunctor_918_);
        leanh::lean_dec_ref(v_inst_912_);
        v_val_919_ = leanh::lean_ctor_get(v_x_914_, 0);
        leanh::lean_inc(v_val_919_);
        leanh::lean_dec_ref_known(v_x_914_, 1);
        v_map_920_ = leanh::lean_ctor_get(v_toFunctor_918_, 0);
        leanh::lean_inc(v_map_920_);
        leanh::lean_dec_ref(v_toFunctor_918_);
        v___f_921_ = l_Option_mapM___redArg___closed__0;
        v___x_922_ = leanh::lean_apply_1(v_f_913_, v_val_919_);
        v___x_923_ = leanh::lean_apply_4(
            v_map_920_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_921_,
            v___x_922_,
        );
        return v___x_923_;
    }
}
pub unsafe fn l_Option_mapM(
    mut v_m_924_: *mut leanh::LeanObject,
    mut v_00_u03b1_925_: *mut leanh::LeanObject,
    mut v_00_u03b2_926_: *mut leanh::LeanObject,
    mut v_inst_927_: *mut leanh::LeanObject,
    mut v_f_928_: *mut leanh::LeanObject,
    mut v_x_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_929_) == 0 {
        let mut v_toPure_930_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_928_);
        v_toPure_930_ = leanh::lean_ctor_get(v_inst_927_, 1);
        leanh::lean_inc(v_toPure_930_);
        leanh::lean_dec_ref(v_inst_927_);
        v___x_931_ = leanh::lean_box(0);
        v___x_932_ =
            leanh::lean_apply_2(v_toPure_930_, leanh::lean_box(0), v___x_931_);
        return v___x_932_;
    } else {
        let mut v_toFunctor_933_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_934_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_935_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_933_ = leanh::lean_ctor_get(v_inst_927_, 0);
        leanh::lean_inc_ref(v_toFunctor_933_);
        leanh::lean_dec_ref(v_inst_927_);
        v_val_934_ = leanh::lean_ctor_get(v_x_929_, 0);
        leanh::lean_inc(v_val_934_);
        leanh::lean_dec_ref_known(v_x_929_, 1);
        v_map_935_ = leanh::lean_ctor_get(v_toFunctor_933_, 0);
        leanh::lean_inc(v_map_935_);
        leanh::lean_dec_ref(v_toFunctor_933_);
        v___f_936_ = l_Option_mapM___redArg___closed__0;
        v___x_937_ = leanh::lean_apply_1(v_f_928_, v_val_934_);
        v___x_938_ = leanh::lean_apply_4(
            v_map_935_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_936_,
            v___x_937_,
        );
        return v___x_938_;
    }
}
pub unsafe fn l_Option_mapA___redArg(
    mut v_inst_939_: *mut leanh::LeanObject,
    mut v_f_940_: *mut leanh::LeanObject,
    mut v_a_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_941_) == 0 {
        let mut v_toPure_942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_940_);
        v_toPure_942_ = leanh::lean_ctor_get(v_inst_939_, 1);
        leanh::lean_inc(v_toPure_942_);
        leanh::lean_dec_ref(v_inst_939_);
        v___x_943_ = leanh::lean_box(0);
        v___x_944_ =
            leanh::lean_apply_2(v_toPure_942_, leanh::lean_box(0), v___x_943_);
        return v___x_944_;
    } else {
        let mut v_toFunctor_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_945_ = leanh::lean_ctor_get(v_inst_939_, 0);
        leanh::lean_inc_ref(v_toFunctor_945_);
        leanh::lean_dec_ref(v_inst_939_);
        v_val_946_ = leanh::lean_ctor_get(v_a_941_, 0);
        leanh::lean_inc(v_val_946_);
        leanh::lean_dec_ref_known(v_a_941_, 1);
        v_map_947_ = leanh::lean_ctor_get(v_toFunctor_945_, 0);
        leanh::lean_inc(v_map_947_);
        leanh::lean_dec_ref(v_toFunctor_945_);
        v___f_948_ = l_Option_mapM___redArg___closed__0;
        v___x_949_ = leanh::lean_apply_1(v_f_940_, v_val_946_);
        v___x_950_ = leanh::lean_apply_4(
            v_map_947_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_948_,
            v___x_949_,
        );
        return v___x_950_;
    }
}
pub unsafe fn l_Option_mapA(
    mut v_m_951_: *mut leanh::LeanObject,
    mut v_00_u03b1_952_: *mut leanh::LeanObject,
    mut v_00_u03b2_953_: *mut leanh::LeanObject,
    mut v_inst_954_: *mut leanh::LeanObject,
    mut v_f_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_956_) == 0 {
        let mut v_toPure_957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_955_);
        v_toPure_957_ = leanh::lean_ctor_get(v_inst_954_, 1);
        leanh::lean_inc(v_toPure_957_);
        leanh::lean_dec_ref(v_inst_954_);
        v___x_958_ = leanh::lean_box(0);
        v___x_959_ =
            leanh::lean_apply_2(v_toPure_957_, leanh::lean_box(0), v___x_958_);
        return v___x_959_;
    } else {
        let mut v_toFunctor_960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_960_ = leanh::lean_ctor_get(v_inst_954_, 0);
        leanh::lean_inc_ref(v_toFunctor_960_);
        leanh::lean_dec_ref(v_inst_954_);
        v_val_961_ = leanh::lean_ctor_get(v_a_956_, 0);
        leanh::lean_inc(v_val_961_);
        leanh::lean_dec_ref_known(v_a_956_, 1);
        v_map_962_ = leanh::lean_ctor_get(v_toFunctor_960_, 0);
        leanh::lean_inc(v_map_962_);
        leanh::lean_dec_ref(v_toFunctor_960_);
        v___f_963_ = l_Option_mapM___redArg___closed__0;
        v___x_964_ = leanh::lean_apply_1(v_f_955_, v_val_961_);
        v___x_965_ = leanh::lean_apply_4(
            v_map_962_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_963_,
            v___x_964_,
        );
        return v___x_965_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0(
    mut v_x_966_: *mut leanh::LeanObject,
    mut v_b_967_: u8,
) -> *mut leanh::LeanObject {
    if v_b_967_ == 0 {
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_968_ = leanh::lean_box(0);
        return v___x_968_;
    } else {
        leanh::lean_inc(v_x_966_);
        return v_x_966_;
    }
}
pub unsafe fn l_Option_filterM___redArg___lam__0___boxed(
    mut v_x_969_: *mut leanh::LeanObject,
    mut v_b_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_971_: u8 = 0;
    let mut v_res_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_971_ = (leanh::lean_unbox(v_b_970_) as u8);
    v_res_972_ = l_Option_filterM___redArg___lam__0(v_x_969_, v_b_boxed_971_);
    leanh::lean_dec(v_x_969_);
    return v_res_972_;
}
pub unsafe fn l_Option_filterM___redArg(
    mut v_inst_973_: *mut leanh::LeanObject,
    mut v_p_974_: *mut leanh::LeanObject,
    mut v_x_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_975_) == 0 {
        let mut v_toPure_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_974_);
        v_toPure_976_ = leanh::lean_ctor_get(v_inst_973_, 1);
        leanh::lean_inc(v_toPure_976_);
        leanh::lean_dec_ref(v_inst_973_);
        v___x_977_ = leanh::lean_apply_2(v_toPure_976_, leanh::lean_box(0), v_x_975_);
        return v___x_977_;
    } else {
        let mut v_toFunctor_978_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_979_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_980_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_978_ = leanh::lean_ctor_get(v_inst_973_, 0);
        leanh::lean_inc_ref(v_toFunctor_978_);
        leanh::lean_dec_ref(v_inst_973_);
        v_val_979_ = leanh::lean_ctor_get(v_x_975_, 0);
        leanh::lean_inc(v_val_979_);
        v_map_980_ = leanh::lean_ctor_get(v_toFunctor_978_, 0);
        leanh::lean_inc(v_map_980_);
        leanh::lean_dec_ref(v_toFunctor_978_);
        v___f_981_ = leanh::lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_981_, 0, v_x_975_);
        v___x_982_ = leanh::lean_apply_1(v_p_974_, v_val_979_);
        v___x_983_ = leanh::lean_apply_4(
            v_map_980_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_981_,
            v___x_982_,
        );
        return v___x_983_;
    }
}
pub unsafe fn l_Option_filterM(
    mut v_m_984_: *mut leanh::LeanObject,
    mut v_00_u03b1_985_: *mut leanh::LeanObject,
    mut v_inst_986_: *mut leanh::LeanObject,
    mut v_p_987_: *mut leanh::LeanObject,
    mut v_x_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_988_) == 0 {
        let mut v_toPure_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_987_);
        v_toPure_989_ = leanh::lean_ctor_get(v_inst_986_, 1);
        leanh::lean_inc(v_toPure_989_);
        leanh::lean_dec_ref(v_inst_986_);
        v___x_990_ = leanh::lean_apply_2(v_toPure_989_, leanh::lean_box(0), v_x_988_);
        return v___x_990_;
    } else {
        let mut v_toFunctor_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_993_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_994_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_991_ = leanh::lean_ctor_get(v_inst_986_, 0);
        leanh::lean_inc_ref(v_toFunctor_991_);
        leanh::lean_dec_ref(v_inst_986_);
        v_val_992_ = leanh::lean_ctor_get(v_x_988_, 0);
        leanh::lean_inc(v_val_992_);
        v_map_993_ = leanh::lean_ctor_get(v_toFunctor_991_, 0);
        leanh::lean_inc(v_map_993_);
        leanh::lean_dec_ref(v_toFunctor_991_);
        v___f_994_ = leanh::lean_alloc_closure(
            l_Option_filterM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_994_, 0, v_x_988_);
        v___x_995_ = leanh::lean_apply_1(v_p_987_, v_val_992_);
        v___x_996_ = leanh::lean_apply_4(
            v_map_993_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_994_,
            v___x_995_,
        );
        return v___x_996_;
    }
}
pub unsafe fn l_Option_filter___redArg(
    mut v_p_997_: *mut leanh::LeanObject,
    mut v_x_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_998_) == 0 {
        leanh::lean_dec_ref(v_p_997_);
        return v_x_998_;
    } else {
        let mut v_val_999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1001_: u8 = 0;
        v_val_999_ = leanh::lean_ctor_get(v_x_998_, 0);
        leanh::lean_inc(v_val_999_);
        v___x_1000_ = leanh::lean_apply_1(v_p_997_, v_val_999_);
        v___x_1001_ = (leanh::lean_unbox(v___x_1000_) as u8);
        if v___x_1001_ == 0 {
            let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_x_998_, 1);
            v___x_1002_ = leanh::lean_box(0);
            return v___x_1002_;
        } else {
            return v_x_998_;
        }
    }
}
pub unsafe fn l_Option_filter(
    mut v_00_u03b1_1003_: *mut leanh::LeanObject,
    mut v_p_1004_: *mut leanh::LeanObject,
    mut v_x_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1005_) == 0 {
        leanh::lean_dec_ref(v_p_1004_);
        return v_x_1005_;
    } else {
        let mut v_val_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: u8 = 0;
        v_val_1006_ = leanh::lean_ctor_get(v_x_1005_, 0);
        leanh::lean_inc(v_val_1006_);
        v___x_1007_ = leanh::lean_apply_1(v_p_1004_, v_val_1006_);
        v___x_1008_ = (leanh::lean_unbox(v___x_1007_) as u8);
        if v___x_1008_ == 0 {
            let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_x_1005_, 1);
            v___x_1009_ = leanh::lean_box(0);
            return v___x_1009_;
        } else {
            return v_x_1005_;
        }
    }
}
pub unsafe fn l_Option_all___redArg(
    mut v_p_1010_: *mut leanh::LeanObject,
    mut v_x_1011_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1011_) == 0 {
        let mut v___x_1012_: u8 = 0;
        leanh::lean_dec_ref(v_p_1010_);
        v___x_1012_ = 1;
        return v___x_1012_;
    } else {
        let mut v_val_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1015_: u8 = 0;
        v_val_1013_ = leanh::lean_ctor_get(v_x_1011_, 0);
        leanh::lean_inc(v_val_1013_);
        leanh::lean_dec_ref_known(v_x_1011_, 1);
        v___x_1014_ = leanh::lean_apply_1(v_p_1010_, v_val_1013_);
        v___x_1015_ = (leanh::lean_unbox(v___x_1014_) as u8);
        return v___x_1015_;
    }
}
pub unsafe fn l_Option_all___redArg___boxed(
    mut v_p_1016_: *mut leanh::LeanObject,
    mut v_x_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: u8 = 0;
    let mut v_r_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Option_all___redArg(v_p_1016_, v_x_1017_);
    v_r_1019_ = leanh::lean_box((v_res_1018_) as usize);
    return v_r_1019_;
}
pub unsafe fn l_Option_all(
    mut v_00_u03b1_1020_: *mut leanh::LeanObject,
    mut v_p_1021_: *mut leanh::LeanObject,
    mut v_x_1022_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1022_) == 0 {
        let mut v___x_1023_: u8 = 0;
        leanh::lean_dec_ref(v_p_1021_);
        v___x_1023_ = 1;
        return v___x_1023_;
    } else {
        let mut v_val_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: u8 = 0;
        v_val_1024_ = leanh::lean_ctor_get(v_x_1022_, 0);
        leanh::lean_inc(v_val_1024_);
        leanh::lean_dec_ref_known(v_x_1022_, 1);
        v___x_1025_ = leanh::lean_apply_1(v_p_1021_, v_val_1024_);
        v___x_1026_ = (leanh::lean_unbox(v___x_1025_) as u8);
        return v___x_1026_;
    }
}
pub unsafe fn l_Option_all___boxed(
    mut v_00_u03b1_1027_: *mut leanh::LeanObject,
    mut v_p_1028_: *mut leanh::LeanObject,
    mut v_x_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1030_: u8 = 0;
    let mut v_r_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_Option_all(v_00_u03b1_1027_, v_p_1028_, v_x_1029_);
    v_r_1031_ = leanh::lean_box((v_res_1030_) as usize);
    return v_r_1031_;
}
pub unsafe fn l_Option_any___redArg(
    mut v_p_1032_: *mut leanh::LeanObject,
    mut v_x_1033_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1033_) == 0 {
        let mut v___x_1034_: u8 = 0;
        leanh::lean_dec_ref(v_p_1032_);
        v___x_1034_ = 0;
        return v___x_1034_;
    } else {
        let mut v_val_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: u8 = 0;
        v_val_1035_ = leanh::lean_ctor_get(v_x_1033_, 0);
        leanh::lean_inc(v_val_1035_);
        leanh::lean_dec_ref_known(v_x_1033_, 1);
        v___x_1036_ = leanh::lean_apply_1(v_p_1032_, v_val_1035_);
        v___x_1037_ = (leanh::lean_unbox(v___x_1036_) as u8);
        return v___x_1037_;
    }
}
pub unsafe fn l_Option_any___redArg___boxed(
    mut v_p_1038_: *mut leanh::LeanObject,
    mut v_x_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1040_: u8 = 0;
    let mut v_r_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1040_ = l_Option_any___redArg(v_p_1038_, v_x_1039_);
    v_r_1041_ = leanh::lean_box((v_res_1040_) as usize);
    return v_r_1041_;
}
pub unsafe fn l_Option_any(
    mut v_00_u03b1_1042_: *mut leanh::LeanObject,
    mut v_p_1043_: *mut leanh::LeanObject,
    mut v_x_1044_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1044_) == 0 {
        let mut v___x_1045_: u8 = 0;
        leanh::lean_dec_ref(v_p_1043_);
        v___x_1045_ = 0;
        return v___x_1045_;
    } else {
        let mut v_val_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: u8 = 0;
        v_val_1046_ = leanh::lean_ctor_get(v_x_1044_, 0);
        leanh::lean_inc(v_val_1046_);
        leanh::lean_dec_ref_known(v_x_1044_, 1);
        v___x_1047_ = leanh::lean_apply_1(v_p_1043_, v_val_1046_);
        v___x_1048_ = (leanh::lean_unbox(v___x_1047_) as u8);
        return v___x_1048_;
    }
}
pub unsafe fn l_Option_any___boxed(
    mut v_00_u03b1_1049_: *mut leanh::LeanObject,
    mut v_p_1050_: *mut leanh::LeanObject,
    mut v_x_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1052_: u8 = 0;
    let mut v_r_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1052_ = l_Option_any(v_00_u03b1_1049_, v_p_1050_, v_x_1051_);
    v_r_1053_ = leanh::lean_box((v_res_1052_) as usize);
    return v_r_1053_;
}
pub unsafe fn l_Option_instOrElse___lam__0(
    mut v_x_1054_: *mut leanh::LeanObject,
    mut v_x_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1054_) == 0 {
        let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1056_ = leanh::lean_box(0);
        v___x_1057_ = leanh::lean_apply_1(v_x_1055_, v___x_1056_);
        return v___x_1057_;
    } else {
        leanh::lean_dec_ref(v_x_1055_);
        leanh::lean_inc_ref(v_x_1054_);
        return v_x_1054_;
    }
}
pub unsafe fn l_Option_instOrElse___lam__0___boxed(
    mut v_x_1058_: *mut leanh::LeanObject,
    mut v_x_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Option_instOrElse___lam__0(v_x_1058_, v_x_1059_);
    leanh::lean_dec(v_x_1058_);
    return v_res_1060_;
}
pub unsafe fn l_Option_instOrElse(
    mut v_00_u03b1_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1063_ = l_Option_instOrElse___closed__0;
    return v___f_1063_;
}
pub unsafe fn l_Option_instDecidableRelLt___redArg(
    mut v_s_1064_: *mut leanh::LeanObject,
    mut v_x_1065_: *mut leanh::LeanObject,
    mut v_x_1066_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1065_) == 0 {
        leanh::lean_dec_ref(v_s_1064_);
        if leanh::lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1067_: u8 = 0;
            v___x_1067_ = 0;
            return v___x_1067_;
        } else {
            let mut v___x_1068_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_1066_, 1);
            v___x_1068_ = 1;
            return v___x_1068_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1066_) == 0 {
            let mut v___x_1069_: u8 = 0;
            leanh::lean_dec_ref_known(v_x_1065_, 1);
            leanh::lean_dec_ref(v_s_1064_);
            v___x_1069_ = 0;
            return v___x_1069_;
        } else {
            let mut v_val_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1073_: u8 = 0;
            v_val_1070_ = leanh::lean_ctor_get(v_x_1065_, 0);
            leanh::lean_inc(v_val_1070_);
            leanh::lean_dec_ref_known(v_x_1065_, 1);
            v_val_1071_ = leanh::lean_ctor_get(v_x_1066_, 0);
            leanh::lean_inc(v_val_1071_);
            leanh::lean_dec_ref_known(v_x_1066_, 1);
            v___x_1072_ = leanh::lean_apply_2(v_s_1064_, v_val_1070_, v_val_1071_);
            v___x_1073_ = (leanh::lean_unbox(v___x_1072_) as u8);
            return v___x_1073_;
        }
    }
}
pub unsafe fn l_Option_instDecidableRelLt___redArg___boxed(
    mut v_s_1074_: *mut leanh::LeanObject,
    mut v_x_1075_: *mut leanh::LeanObject,
    mut v_x_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1077_: u8 = 0;
    let mut v_r_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Option_instDecidableRelLt___redArg(v_s_1074_, v_x_1075_, v_x_1076_);
    v_r_1078_ = leanh::lean_box((v_res_1077_) as usize);
    return v_r_1078_;
}
pub unsafe fn l_Option_instDecidableRelLt(
    mut v_00_u03b1_1079_: *mut leanh::LeanObject,
    mut v_00_u03b2_1080_: *mut leanh::LeanObject,
    mut v_r_1081_: *mut leanh::LeanObject,
    mut v_s_1082_: *mut leanh::LeanObject,
    mut v_x_1083_: *mut leanh::LeanObject,
    mut v_x_1084_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1085_: u8 = 0;
    v___x_1085_ = l_Option_instDecidableRelLt___redArg(v_s_1082_, v_x_1083_, v_x_1084_);
    return v___x_1085_;
}
pub unsafe fn l_Option_instDecidableRelLt___boxed(
    mut v_00_u03b1_1086_: *mut leanh::LeanObject,
    mut v_00_u03b2_1087_: *mut leanh::LeanObject,
    mut v_r_1088_: *mut leanh::LeanObject,
    mut v_s_1089_: *mut leanh::LeanObject,
    mut v_x_1090_: *mut leanh::LeanObject,
    mut v_x_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: u8 = 0;
    let mut v_r_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Option_instDecidableRelLt(
        v_00_u03b1_1086_,
        v_00_u03b2_1087_,
        v_r_1088_,
        v_s_1089_,
        v_x_1090_,
        v_x_1091_,
    );
    v_r_1093_ = leanh::lean_box((v_res_1092_) as usize);
    return v_r_1093_;
}
pub unsafe fn l_Option_merge___redArg(
    mut v_fn_1094_: *mut leanh::LeanObject,
    mut v_x_1095_: *mut leanh::LeanObject,
    mut v_x_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1095_) == 0 {
                    leanh::lean_dec(v_fn_1094_);
                    return v_x_1096_;
                } else {
                    if leanh::lean_obj_tag(v_x_1096_) == 0 {
                        leanh::lean_dec(v_fn_1094_);
                        return v_x_1095_;
                    } else {
                        v_val_1097_ = leanh::lean_ctor_get(v_x_1095_, 0);
                        leanh::lean_inc(v_val_1097_);
                        leanh::lean_dec_ref_known(v_x_1095_, 1);
                        v_val_1098_ = leanh::lean_ctor_get(v_x_1096_, 0);
                        v_isSharedCheck_1106_ = (!leanh::lean_is_exclusive(v_x_1096_)) as u8;
                        if v_isSharedCheck_1106_ == 0 {
                            v___x_1100_ = v_x_1096_;
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1098_);
                            leanh::lean_dec(v_x_1096_);
                            v___x_1100_ = leanh::lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1106_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1102_ = leanh::lean_apply_2(v_fn_1094_, v_val_1097_, v_val_1098_);
                if v_isShared_1101_ == 0 {
                    leanh::lean_ctor_set(v___x_1100_, 0, v___x_1102_);
                    v___x_1104_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
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
    mut v_00_u03b1_1107_: *mut leanh::LeanObject,
    mut v_fn_1108_: *mut leanh::LeanObject,
    mut v_x_1109_: *mut leanh::LeanObject,
    mut v_x_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Option_merge___redArg(v_fn_1108_, v_x_1109_, v_x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Option_elim___redArg(
    mut v_x_1112_: *mut leanh::LeanObject,
    mut v_x_1113_: *mut leanh::LeanObject,
    mut v_x_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1112_) == 0 {
        leanh::lean_dec(v_x_1114_);
        leanh::lean_inc(v_x_1113_);
        return v_x_1113_;
    } else {
        let mut v_val_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1115_ = leanh::lean_ctor_get(v_x_1112_, 0);
        leanh::lean_inc(v_val_1115_);
        leanh::lean_dec_ref_known(v_x_1112_, 1);
        v___x_1116_ = leanh::lean_apply_1(v_x_1114_, v_val_1115_);
        return v___x_1116_;
    }
}
pub unsafe fn l_Option_elim___redArg___boxed(
    mut v_x_1117_: *mut leanh::LeanObject,
    mut v_x_1118_: *mut leanh::LeanObject,
    mut v_x_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Option_elim___redArg(v_x_1117_, v_x_1118_, v_x_1119_);
    leanh::lean_dec(v_x_1118_);
    return v_res_1120_;
}
pub unsafe fn l_Option_elim(
    mut v_00_u03b1_1121_: *mut leanh::LeanObject,
    mut v_00_u03b2_1122_: *mut leanh::LeanObject,
    mut v_x_1123_: *mut leanh::LeanObject,
    mut v_x_1124_: *mut leanh::LeanObject,
    mut v_x_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1123_) == 0 {
        leanh::lean_dec(v_x_1125_);
        leanh::lean_inc(v_x_1124_);
        return v_x_1124_;
    } else {
        let mut v_val_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1126_ = leanh::lean_ctor_get(v_x_1123_, 0);
        leanh::lean_inc(v_val_1126_);
        leanh::lean_dec_ref_known(v_x_1123_, 1);
        v___x_1127_ = leanh::lean_apply_1(v_x_1125_, v_val_1126_);
        return v___x_1127_;
    }
}
pub unsafe fn l_Option_elim___boxed(
    mut v_00_u03b1_1128_: *mut leanh::LeanObject,
    mut v_00_u03b2_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
    mut v_x_1131_: *mut leanh::LeanObject,
    mut v_x_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Option_elim(
        v_00_u03b1_1128_,
        v_00_u03b2_1129_,
        v_x_1130_,
        v_x_1131_,
        v_x_1132_,
    );
    leanh::lean_dec(v_x_1131_);
    return v_res_1133_;
}
pub unsafe fn l_Option_get___redArg(
    mut v_x_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_1135_ = leanh::lean_ctor_get(v_x_1134_, 0);
    leanh::lean_inc(v_val_1135_);
    return v_val_1135_;
}
pub unsafe fn l_Option_get___redArg___boxed(
    mut v_x_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Option_get___redArg(v_x_1136_);
    leanh::lean_dec(v_x_1136_);
    return v_res_1137_;
}
pub unsafe fn l_Option_get(
    mut v_00_u03b1_1138_: *mut leanh::LeanObject,
    mut v_x_1139_: *mut leanh::LeanObject,
    mut v_x_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_1141_ = leanh::lean_ctor_get(v_x_1139_, 0);
    leanh::lean_inc(v_val_1141_);
    return v_val_1141_;
}
pub unsafe fn l_Option_get___boxed(
    mut v_00_u03b1_1142_: *mut leanh::LeanObject,
    mut v_x_1143_: *mut leanh::LeanObject,
    mut v_x_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Option_get(v_00_u03b1_1142_, v_x_1143_, v_x_1144_);
    leanh::lean_dec(v_x_1143_);
    return v_res_1145_;
}
pub unsafe fn l_Option_guard___redArg(
    mut v_p_1146_: *mut leanh::LeanObject,
    mut v_a_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: u8 = 0;
    leanh::lean_inc(v_a_1147_);
    v___x_1148_ = leanh::lean_apply_1(v_p_1146_, v_a_1147_);
    v___x_1149_ = (leanh::lean_unbox(v___x_1148_) as u8);
    if v___x_1149_ == 0 {
        let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1147_);
        v___x_1150_ = leanh::lean_box(0);
        return v___x_1150_;
    } else {
        let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1151_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1151_, 0, v_a_1147_);
        return v___x_1151_;
    }
}
pub unsafe fn l_Option_guard(
    mut v_00_u03b1_1152_: *mut leanh::LeanObject,
    mut v_p_1153_: *mut leanh::LeanObject,
    mut v_a_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    leanh::lean_inc(v_a_1154_);
    v___x_1155_ = leanh::lean_apply_1(v_p_1153_, v_a_1154_);
    v___x_1156_ = (leanh::lean_unbox(v___x_1155_) as u8);
    if v___x_1156_ == 0 {
        let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1154_);
        v___x_1157_ = leanh::lean_box(0);
        return v___x_1157_;
    } else {
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1158_, 0, v_a_1154_);
        return v___x_1158_;
    }
}
pub unsafe fn l_Option_toList___redArg(
    mut v_x_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1159_) == 0 {
        let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1160_ = leanh::lean_box(0);
        return v___x_1160_;
    } else {
        let mut v_val_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1161_ = leanh::lean_ctor_get(v_x_1159_, 0);
        v___x_1162_ = leanh::lean_box(0);
        leanh::lean_inc(v_val_1161_);
        v___x_1163_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1163_, 0, v_val_1161_);
        leanh::lean_ctor_set(v___x_1163_, 1, v___x_1162_);
        return v___x_1163_;
    }
}
pub unsafe fn l_Option_toList___redArg___boxed(
    mut v_x_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1165_ = l_Option_toList___redArg(v_x_1164_);
    leanh::lean_dec(v_x_1164_);
    return v_res_1165_;
}
pub unsafe fn l_Option_toList(
    mut v_00_u03b1_1166_: *mut leanh::LeanObject,
    mut v_x_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1167_) == 0 {
        let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1168_ = leanh::lean_box(0);
        return v___x_1168_;
    } else {
        let mut v_val_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1169_ = leanh::lean_ctor_get(v_x_1167_, 0);
        v___x_1170_ = leanh::lean_box(0);
        leanh::lean_inc(v_val_1169_);
        v___x_1171_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1171_, 0, v_val_1169_);
        leanh::lean_ctor_set(v___x_1171_, 1, v___x_1170_);
        return v___x_1171_;
    }
}
pub unsafe fn l_Option_toList___boxed(
    mut v_00_u03b1_1172_: *mut leanh::LeanObject,
    mut v_x_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1174_ = l_Option_toList(v_00_u03b1_1172_, v_x_1173_);
    leanh::lean_dec(v_x_1173_);
    return v_res_1174_;
}
pub unsafe fn l_Option_toArray___redArg(
    mut v_x_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1177_) == 0 {
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1178_ = l_Option_toArray___redArg___closed__0;
        return v___x_1178_;
    } else {
        let mut v_val_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1179_ = leanh::lean_ctor_get(v_x_1177_, 0);
        leanh::lean_inc(v_val_1179_);
        leanh::lean_dec_ref_known(v_x_1177_, 1);
        v___x_1180_ = leanh::lean_unsigned_to_nat(1);
        v___x_1181_ = lean_mk_empty_array_with_capacity(v___x_1180_);
        v___x_1182_ = lean_array_push(v___x_1181_, v_val_1179_);
        return v___x_1182_;
    }
}
pub unsafe fn l_Option_toArray(
    mut v_00_u03b1_1183_: *mut leanh::LeanObject,
    mut v_x_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1184_) == 0 {
        let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1185_ = l_Option_toArray___redArg___closed__0;
        return v___x_1185_;
    } else {
        let mut v_val_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1186_ = leanh::lean_ctor_get(v_x_1184_, 0);
        leanh::lean_inc(v_val_1186_);
        leanh::lean_dec_ref_known(v_x_1184_, 1);
        v___x_1187_ = leanh::lean_unsigned_to_nat(1);
        v___x_1188_ = lean_mk_empty_array_with_capacity(v___x_1187_);
        v___x_1189_ = lean_array_push(v___x_1188_, v_val_1186_);
        return v___x_1189_;
    }
}
pub unsafe fn l_Option_join___redArg(
    mut v_x_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1190_) == 0 {
        let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1191_ = leanh::lean_box(0);
        return v___x_1191_;
    } else {
        let mut v_val_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1192_ = leanh::lean_ctor_get(v_x_1190_, 0);
        leanh::lean_inc(v_val_1192_);
        return v_val_1192_;
    }
}
pub unsafe fn l_Option_join___redArg___boxed(
    mut v_x_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Option_join___redArg(v_x_1193_);
    leanh::lean_dec(v_x_1193_);
    return v_res_1194_;
}
pub unsafe fn l_Option_join(
    mut v_00_u03b1_1195_: *mut leanh::LeanObject,
    mut v_x_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1196_) == 0 {
        let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1197_ = leanh::lean_box(0);
        return v___x_1197_;
    } else {
        let mut v_val_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1198_ = leanh::lean_ctor_get(v_x_1196_, 0);
        leanh::lean_inc(v_val_1198_);
        return v_val_1198_;
    }
}
pub unsafe fn l_Option_join___boxed(
    mut v_00_u03b1_1199_: *mut leanh::LeanObject,
    mut v_x_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Option_join(v_00_u03b1_1199_, v_x_1200_);
    leanh::lean_dec(v_x_1200_);
    return v_res_1201_;
}
pub unsafe fn l_Option_sequence___redArg(
    mut v_inst_1202_: *mut leanh::LeanObject,
    mut v_x_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1203_) == 0 {
        let mut v_toPure_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toPure_1204_ = leanh::lean_ctor_get(v_inst_1202_, 1);
        leanh::lean_inc(v_toPure_1204_);
        leanh::lean_dec_ref(v_inst_1202_);
        v___x_1205_ = leanh::lean_box(0);
        v___x_1206_ =
            leanh::lean_apply_2(v_toPure_1204_, leanh::lean_box(0), v___x_1205_);
        return v___x_1206_;
    } else {
        let mut v_toFunctor_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_1207_ = leanh::lean_ctor_get(v_inst_1202_, 0);
        leanh::lean_inc_ref(v_toFunctor_1207_);
        leanh::lean_dec_ref(v_inst_1202_);
        v_val_1208_ = leanh::lean_ctor_get(v_x_1203_, 0);
        leanh::lean_inc(v_val_1208_);
        leanh::lean_dec_ref_known(v_x_1203_, 1);
        v_map_1209_ = leanh::lean_ctor_get(v_toFunctor_1207_, 0);
        leanh::lean_inc(v_map_1209_);
        leanh::lean_dec_ref(v_toFunctor_1207_);
        v___f_1210_ = l_Option_mapM___redArg___closed__0;
        v___x_1211_ = leanh::lean_apply_4(
            v_map_1209_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_1210_,
            v_val_1208_,
        );
        return v___x_1211_;
    }
}
pub unsafe fn l_Option_sequence(
    mut v_m_1212_: *mut leanh::LeanObject,
    mut v_inst_1213_: *mut leanh::LeanObject,
    mut v_00_u03b1_1214_: *mut leanh::LeanObject,
    mut v_x_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1215_) == 0 {
        let mut v_toPure_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toPure_1216_ = leanh::lean_ctor_get(v_inst_1213_, 1);
        leanh::lean_inc(v_toPure_1216_);
        leanh::lean_dec_ref(v_inst_1213_);
        v___x_1217_ = leanh::lean_box(0);
        v___x_1218_ =
            leanh::lean_apply_2(v_toPure_1216_, leanh::lean_box(0), v___x_1217_);
        return v___x_1218_;
    } else {
        let mut v_toFunctor_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_1219_ = leanh::lean_ctor_get(v_inst_1213_, 0);
        leanh::lean_inc_ref(v_toFunctor_1219_);
        leanh::lean_dec_ref(v_inst_1213_);
        v_val_1220_ = leanh::lean_ctor_get(v_x_1215_, 0);
        leanh::lean_inc(v_val_1220_);
        leanh::lean_dec_ref_known(v_x_1215_, 1);
        v_map_1221_ = leanh::lean_ctor_get(v_toFunctor_1219_, 0);
        leanh::lean_inc(v_map_1221_);
        leanh::lean_dec_ref(v_toFunctor_1219_);
        v___f_1222_ = l_Option_mapM___redArg___closed__0;
        v___x_1223_ = leanh::lean_apply_4(
            v_map_1221_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___f_1222_,
            v_val_1220_,
        );
        return v___x_1223_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0(
    mut v_y_1224_: *mut leanh::LeanObject,
    mut v_z_1225_: *mut leanh::LeanObject,
    mut v_____do__lift_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1226_) == 0 {
        leanh::lean_dec(v_z_1225_);
        leanh::lean_inc(v_y_1224_);
        return v_y_1224_;
    } else {
        let mut v_val_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1227_ = leanh::lean_ctor_get(v_____do__lift_1226_, 0);
        leanh::lean_inc(v_val_1227_);
        leanh::lean_dec_ref_known(v_____do__lift_1226_, 1);
        v___x_1228_ = leanh::lean_apply_1(v_z_1225_, v_val_1227_);
        return v___x_1228_;
    }
}
pub unsafe fn l_Option_elimM___redArg___lam__0___boxed(
    mut v_y_1229_: *mut leanh::LeanObject,
    mut v_z_1230_: *mut leanh::LeanObject,
    mut v_____do__lift_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Option_elimM___redArg___lam__0(v_y_1229_, v_z_1230_, v_____do__lift_1231_);
    leanh::lean_dec(v_y_1229_);
    return v_res_1232_;
}
pub unsafe fn l_Option_elimM___redArg(
    mut v_inst_1233_: *mut leanh::LeanObject,
    mut v_x_1234_: *mut leanh::LeanObject,
    mut v_y_1235_: *mut leanh::LeanObject,
    mut v_z_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1237_ = leanh::lean_ctor_get(v_inst_1233_, 1);
    leanh::lean_inc(v_toBind_1237_);
    leanh::lean_dec_ref(v_inst_1233_);
    v___f_1238_ = leanh::lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1238_, 0, v_y_1235_);
    leanh::lean_closure_set(v___f_1238_, 1, v_z_1236_);
    v___x_1239_ = leanh::lean_apply_4(
        v_toBind_1237_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_1234_,
        v___f_1238_,
    );
    return v___x_1239_;
}
pub unsafe fn l_Option_elimM(
    mut v_m_1240_: *mut leanh::LeanObject,
    mut v_00_u03b1_1241_: *mut leanh::LeanObject,
    mut v_00_u03b2_1242_: *mut leanh::LeanObject,
    mut v_inst_1243_: *mut leanh::LeanObject,
    mut v_x_1244_: *mut leanh::LeanObject,
    mut v_y_1245_: *mut leanh::LeanObject,
    mut v_z_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1247_ = leanh::lean_ctor_get(v_inst_1243_, 1);
    leanh::lean_inc(v_toBind_1247_);
    leanh::lean_dec_ref(v_inst_1243_);
    v___f_1248_ = leanh::lean_alloc_closure(
        l_Option_elimM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1248_, 0, v_y_1245_);
    leanh::lean_closure_set(v___f_1248_, 1, v_z_1246_);
    v___x_1249_ = leanh::lean_apply_4(
        v_toBind_1247_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_1244_,
        v___f_1248_,
    );
    return v___x_1249_;
}
pub unsafe fn l_Option_getDM___redArg(
    mut v_inst_1250_: *mut leanh::LeanObject,
    mut v_x_1251_: *mut leanh::LeanObject,
    mut v_y_1252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1251_) == 0 {
        leanh::lean_dec(v_inst_1250_);
        leanh::lean_inc(v_y_1252_);
        return v_y_1252_;
    } else {
        let mut v_val_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1253_ = leanh::lean_ctor_get(v_x_1251_, 0);
        leanh::lean_inc(v_val_1253_);
        leanh::lean_dec_ref_known(v_x_1251_, 1);
        v___x_1254_ =
            leanh::lean_apply_2(v_inst_1250_, leanh::lean_box(0), v_val_1253_);
        return v___x_1254_;
    }
}
pub unsafe fn l_Option_getDM___redArg___boxed(
    mut v_inst_1255_: *mut leanh::LeanObject,
    mut v_x_1256_: *mut leanh::LeanObject,
    mut v_y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Option_getDM___redArg(v_inst_1255_, v_x_1256_, v_y_1257_);
    leanh::lean_dec(v_y_1257_);
    return v_res_1258_;
}
pub unsafe fn l_Option_getDM(
    mut v_m_1259_: *mut leanh::LeanObject,
    mut v_00_u03b1_1260_: *mut leanh::LeanObject,
    mut v_inst_1261_: *mut leanh::LeanObject,
    mut v_x_1262_: *mut leanh::LeanObject,
    mut v_y_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1262_) == 0 {
        leanh::lean_dec(v_inst_1261_);
        leanh::lean_inc(v_y_1263_);
        return v_y_1263_;
    } else {
        let mut v_val_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1264_ = leanh::lean_ctor_get(v_x_1262_, 0);
        leanh::lean_inc(v_val_1264_);
        leanh::lean_dec_ref_known(v_x_1262_, 1);
        v___x_1265_ =
            leanh::lean_apply_2(v_inst_1261_, leanh::lean_box(0), v_val_1264_);
        return v___x_1265_;
    }
}
pub unsafe fn l_Option_getDM___boxed(
    mut v_m_1266_: *mut leanh::LeanObject,
    mut v_00_u03b1_1267_: *mut leanh::LeanObject,
    mut v_inst_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_y_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_Option_getDM(
        v_m_1266_,
        v_00_u03b1_1267_,
        v_inst_1268_,
        v_x_1269_,
        v_y_1270_,
    );
    leanh::lean_dec(v_y_1270_);
    return v_res_1271_;
}
pub unsafe fn l_Option_min___redArg(
    mut v_inst_1272_: *mut leanh::LeanObject,
    mut v_x_1273_: *mut leanh::LeanObject,
    mut v_x_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1273_) == 0 {
                    leanh::lean_dec(v_inst_1272_);
                    if leanh::lean_obj_tag(v_x_1274_) == 0 {
                        return v_x_1274_;
                    } else {
                        leanh::lean_dec_ref_known(v_x_1274_, 1);
                        return v_x_1273_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_1274_) == 0 {
                        leanh::lean_dec_ref_known(v_x_1273_, 1);
                        leanh::lean_dec(v_inst_1272_);
                        return v_x_1274_;
                    } else {
                        v_val_1275_ = leanh::lean_ctor_get(v_x_1273_, 0);
                        leanh::lean_inc(v_val_1275_);
                        leanh::lean_dec_ref_known(v_x_1273_, 1);
                        v_val_1276_ = leanh::lean_ctor_get(v_x_1274_, 0);
                        v_isSharedCheck_1284_ = (!leanh::lean_is_exclusive(v_x_1274_)) as u8;
                        if v_isSharedCheck_1284_ == 0 {
                            v___x_1278_ = v_x_1274_;
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1276_);
                            leanh::lean_dec(v_x_1274_);
                            v___x_1278_ = leanh::lean_box(0);
                            v_isShared_1279_ = v_isSharedCheck_1284_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1280_ = leanh::lean_apply_2(v_inst_1272_, v_val_1275_, v_val_1276_);
                if v_isShared_1279_ == 0 {
                    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1280_);
                    v___x_1282_ = v___x_1278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
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
    mut v_00_u03b1_1285_: *mut leanh::LeanObject,
    mut v_inst_1286_: *mut leanh::LeanObject,
    mut v_x_1287_: *mut leanh::LeanObject,
    mut v_x_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ = l_Option_min___redArg(v_inst_1286_, v_x_1287_, v_x_1288_);
    return v___x_1289_;
}
pub unsafe fn l_Option_instMin___redArg(
    mut v_inst_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = leanh::lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1291_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1291_, 1, v_inst_1290_);
    return v___x_1291_;
}
pub unsafe fn l_Option_instMin(
    mut v_00_u03b1_1292_: *mut leanh::LeanObject,
    mut v_inst_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = leanh::lean_alloc_closure(l_Option_min as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1294_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1294_, 1, v_inst_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Option_max___redArg(
    mut v_inst_1295_: *mut leanh::LeanObject,
    mut v_x_1296_: *mut leanh::LeanObject,
    mut v_x_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1302_: u8 = 0;
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1296_) == 0 {
                    leanh::lean_dec(v_inst_1295_);
                    return v_x_1297_;
                } else {
                    if leanh::lean_obj_tag(v_x_1297_) == 0 {
                        leanh::lean_dec(v_inst_1295_);
                        return v_x_1296_;
                    } else {
                        v_val_1298_ = leanh::lean_ctor_get(v_x_1296_, 0);
                        leanh::lean_inc(v_val_1298_);
                        leanh::lean_dec_ref_known(v_x_1296_, 1);
                        v_val_1299_ = leanh::lean_ctor_get(v_x_1297_, 0);
                        v_isSharedCheck_1307_ = (!leanh::lean_is_exclusive(v_x_1297_)) as u8;
                        if v_isSharedCheck_1307_ == 0 {
                            v___x_1301_ = v_x_1297_;
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1299_);
                            leanh::lean_dec(v_x_1297_);
                            v___x_1301_ = leanh::lean_box(0);
                            v_isShared_1302_ = v_isSharedCheck_1307_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1303_ = leanh::lean_apply_2(v_inst_1295_, v_val_1298_, v_val_1299_);
                if v_isShared_1302_ == 0 {
                    leanh::lean_ctor_set(v___x_1301_, 0, v___x_1303_);
                    v___x_1305_ = v___x_1301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
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
    mut v_00_u03b1_1308_: *mut leanh::LeanObject,
    mut v_inst_1309_: *mut leanh::LeanObject,
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v_x_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Option_max___redArg(v_inst_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Option_instMax___redArg(
    mut v_inst_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = leanh::lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1314_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1314_, 1, v_inst_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Option_instMax(
    mut v_00_u03b1_1315_: *mut leanh::LeanObject,
    mut v_inst_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = leanh::lean_alloc_closure(l_Option_max as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1317_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1317_, 1, v_inst_1316_);
    return v___x_1317_;
}
pub unsafe fn l_instLTOption(
    mut v_00_u03b1_1318_: *mut leanh::LeanObject,
    mut v_inst_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = leanh::lean_box(0);
    return v___x_1320_;
}
pub unsafe fn l_instLEOption(
    mut v_00_u03b1_1321_: *mut leanh::LeanObject,
    mut v_inst_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = leanh::lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_instFunctorOption___lam__0(
    mut v_00_u03b1_1324_: *mut leanh::LeanObject,
    mut v_00_u03b2_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1331_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1335_: u8 = 0;
    let mut v_unused_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1327_) == 0 {
                    leanh::lean_dec(v___y_1326_);
                    v___x_1328_ = leanh::lean_box(0);
                    return v___x_1328_;
                } else {
                    v_isSharedCheck_1335_ = (!leanh::lean_is_exclusive(v___y_1327_)) as u8;
                    if v_isSharedCheck_1335_ == 0 {
                        v_unused_1336_ = leanh::lean_ctor_get(v___y_1327_, 0);
                        leanh::lean_dec(v_unused_1336_);
                        v___x_1330_ = v___y_1327_;
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1327_);
                        v___x_1330_ = leanh::lean_box(0);
                        v_isShared_1331_ = v_isSharedCheck_1335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1331_ == 0 {
                    leanh::lean_ctor_set(v___x_1330_, 0, v___y_1326_);
                    v___x_1333_ = v___x_1330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___y_1326_);
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
    mut v_00_u03b1_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1345_, 0, v___y_1344_);
    return v___x_1345_;
}
pub unsafe fn l_instMonadOption___lam__1(
    mut v_00_u03b1_1346_: *mut leanh::LeanObject,
    mut v_00_u03b2_1347_: *mut leanh::LeanObject,
    mut v_f_1348_: *mut leanh::LeanObject,
    mut v_x_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_f_1348_) == 0 {
                    leanh::lean_dec_ref(v_x_1349_);
                    v___x_1350_ = leanh::lean_box(0);
                    return v___x_1350_;
                } else {
                    v_val_1351_ = leanh::lean_ctor_get(v_f_1348_, 0);
                    leanh::lean_inc(v_val_1351_);
                    leanh::lean_dec_ref_known(v_f_1348_, 1);
                    v___x_1352_ = leanh::lean_box(0);
                    v___x_1353_ = leanh::lean_apply_1(v_x_1349_, v___x_1352_);
                    if leanh::lean_obj_tag(v___x_1353_) == 0 {
                        leanh::lean_dec(v_val_1351_);
                        v___x_1354_ = leanh::lean_box(0);
                        return v___x_1354_;
                    } else {
                        v_val_1355_ = leanh::lean_ctor_get(v___x_1353_, 0);
                        v_isSharedCheck_1363_ =
                            (!leanh::lean_is_exclusive(v___x_1353_)) as u8;
                        if v_isSharedCheck_1363_ == 0 {
                            v___x_1357_ = v___x_1353_;
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1355_);
                            leanh::lean_dec(v___x_1353_);
                            v___x_1357_ = leanh::lean_box(0);
                            v_isShared_1358_ = v_isSharedCheck_1363_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1359_ = leanh::lean_apply_1(v_val_1351_, v_val_1355_);
                if v_isShared_1358_ == 0 {
                    leanh::lean_ctor_set(v___x_1357_, 0, v___x_1359_);
                    v___x_1361_ = v___x_1357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1359_);
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
    mut v_00_u03b1_1364_: *mut leanh::LeanObject,
    mut v_00_u03b2_1365_: *mut leanh::LeanObject,
    mut v_x_1366_: *mut leanh::LeanObject,
    mut v_y_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1366_) == 0 {
        leanh::lean_dec_ref(v_y_1367_);
        return v_x_1366_;
    } else {
        let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1368_ = leanh::lean_box(0);
        v___x_1369_ = leanh::lean_apply_1(v_y_1367_, v___x_1368_);
        if leanh::lean_obj_tag(v___x_1369_) == 0 {
            let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1370_ = leanh::lean_box(0);
            return v___x_1370_;
        } else {
            leanh::lean_dec_ref_known(v___x_1369_, 1);
            leanh::lean_inc_ref(v_x_1366_);
            return v_x_1366_;
        }
    }
}
pub unsafe fn l_instMonadOption___lam__2___boxed(
    mut v_00_u03b1_1371_: *mut leanh::LeanObject,
    mut v_00_u03b2_1372_: *mut leanh::LeanObject,
    mut v_x_1373_: *mut leanh::LeanObject,
    mut v_y_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l_instMonadOption___lam__2(v_00_u03b1_1371_, v_00_u03b2_1372_, v_x_1373_, v_y_1374_);
    leanh::lean_dec(v_x_1373_);
    return v_res_1375_;
}
pub unsafe fn l_instMonadOption___lam__3(
    mut v_00_u03b1_1376_: *mut leanh::LeanObject,
    mut v_00_u03b2_1377_: *mut leanh::LeanObject,
    mut v_x_1378_: *mut leanh::LeanObject,
    mut v_y_1379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1378_) == 0 {
        let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_y_1379_);
        v___x_1380_ = leanh::lean_box(0);
        return v___x_1380_;
    } else {
        let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1381_ = leanh::lean_box(0);
        v___x_1382_ = leanh::lean_apply_1(v_y_1379_, v___x_1381_);
        return v___x_1382_;
    }
}
pub unsafe fn l_instMonadOption___lam__3___boxed(
    mut v_00_u03b1_1383_: *mut leanh::LeanObject,
    mut v_00_u03b2_1384_: *mut leanh::LeanObject,
    mut v_x_1385_: *mut leanh::LeanObject,
    mut v_y_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ =
        l_instMonadOption___lam__3(v_00_u03b1_1383_, v_00_u03b2_1384_, v_x_1385_, v_y_1386_);
    leanh::lean_dec(v_x_1385_);
    return v_res_1387_;
}
pub unsafe fn l_instAlternativeOption___lam__0(
    mut v_00_u03b1_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = leanh::lean_box(0);
    return v___x_1404_;
}
pub unsafe fn l_instAlternativeOption___lam__1(
    mut v_00_u03b1_1405_: *mut leanh::LeanObject,
    mut v_x_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1406_) == 0 {
        let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1408_ = leanh::lean_box(0);
        v___x_1409_ = leanh::lean_apply_1(v_x_1407_, v___x_1408_);
        return v___x_1409_;
    } else {
        leanh::lean_dec_ref(v_x_1407_);
        leanh::lean_inc_ref(v_x_1406_);
        return v_x_1406_;
    }
}
pub unsafe fn l_instAlternativeOption___lam__1___boxed(
    mut v_00_u03b1_1410_: *mut leanh::LeanObject,
    mut v_x_1411_: *mut leanh::LeanObject,
    mut v_x_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1413_ = l_instAlternativeOption___lam__1(v_00_u03b1_1410_, v_x_1411_, v_x_1412_);
    leanh::lean_dec(v_x_1411_);
    return v_res_1413_;
}
pub unsafe fn l_liftOption___redArg(
    mut v_inst_1421_: *mut leanh::LeanObject,
    mut v_x_1422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1422_) == 0 {
        let mut v_failure_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_failure_1423_ = leanh::lean_ctor_get(v_inst_1421_, 1);
        leanh::lean_inc(v_failure_1423_);
        leanh::lean_dec_ref(v_inst_1421_);
        v___x_1424_ = leanh::lean_apply_1(v_failure_1423_, leanh::lean_box(0));
        return v___x_1424_;
    } else {
        let mut v_toApplicative_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1425_ = leanh::lean_ctor_get(v_inst_1421_, 0);
        leanh::lean_inc_ref(v_toApplicative_1425_);
        leanh::lean_dec_ref(v_inst_1421_);
        v_toPure_1426_ = leanh::lean_ctor_get(v_toApplicative_1425_, 1);
        leanh::lean_inc(v_toPure_1426_);
        leanh::lean_dec_ref(v_toApplicative_1425_);
        v_val_1427_ = leanh::lean_ctor_get(v_x_1422_, 0);
        leanh::lean_inc(v_val_1427_);
        leanh::lean_dec_ref_known(v_x_1422_, 1);
        v___x_1428_ =
            leanh::lean_apply_2(v_toPure_1426_, leanh::lean_box(0), v_val_1427_);
        return v___x_1428_;
    }
}
pub unsafe fn l_liftOption(
    mut v_m_1429_: *mut leanh::LeanObject,
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_x_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_liftOption___redArg(v_inst_1431_, v_x_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Option_tryCatch___redArg(
    mut v_x_1434_: *mut leanh::LeanObject,
    mut v_handle_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1434_) == 0 {
        let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1436_ = leanh::lean_box(0);
        v___x_1437_ = leanh::lean_apply_1(v_handle_1435_, v___x_1436_);
        return v___x_1437_;
    } else {
        leanh::lean_dec_ref(v_handle_1435_);
        leanh::lean_inc_ref(v_x_1434_);
        return v_x_1434_;
    }
}
pub unsafe fn l_Option_tryCatch___redArg___boxed(
    mut v_x_1438_: *mut leanh::LeanObject,
    mut v_handle_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Option_tryCatch___redArg(v_x_1438_, v_handle_1439_);
    leanh::lean_dec(v_x_1438_);
    return v_res_1440_;
}
pub unsafe fn l_Option_tryCatch(
    mut v_00_u03b1_1441_: *mut leanh::LeanObject,
    mut v_x_1442_: *mut leanh::LeanObject,
    mut v_handle_1443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1442_) == 0 {
        let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1444_ = leanh::lean_box(0);
        v___x_1445_ = leanh::lean_apply_1(v_handle_1443_, v___x_1444_);
        return v___x_1445_;
    } else {
        leanh::lean_dec_ref(v_handle_1443_);
        leanh::lean_inc_ref(v_x_1442_);
        return v_x_1442_;
    }
}
pub unsafe fn l_Option_tryCatch___boxed(
    mut v_00_u03b1_1446_: *mut leanh::LeanObject,
    mut v_x_1447_: *mut leanh::LeanObject,
    mut v_handle_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_Option_tryCatch(v_00_u03b1_1446_, v_x_1447_, v_handle_1448_);
    leanh::lean_dec(v_x_1447_);
    return v_res_1449_;
}
pub unsafe fn l_instMonadExceptOfUnitOption___lam__0(
    mut v_00_u03b1_1450_: *mut leanh::LeanObject,
    mut v_x_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = leanh::lean_box(0);
    return v___x_1452_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Basic(builtin);
}