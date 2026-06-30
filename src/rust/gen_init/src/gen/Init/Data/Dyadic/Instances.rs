// Lean compiler output
// Module: Init.Data.Dyadic.Instances
// Imports: Init.Data.Dyadic.Basic Init.Grind.Ordered.Ring Init.Data.Rat.Lemmas
use crate::r#gen::Init::Data::Dyadic::Basic::{
    initialize_Init_Data_Dyadic_Basic, l_Dyadic_add, l_Dyadic_instNatCast___lam__0,
    l_Dyadic_instOfNat, l_Dyadic_mul, l_Dyadic_mul___boxed, l_Dyadic_neg, l_Dyadic_ofInt,
    l_Dyadic_pow, l_Dyadic_sub, runtime_initialize_Init_Data_Dyadic_Basic,
};
use crate::r#gen::Init::Data::Rat::Lemmas::{
    initialize_Init_Data_Rat_Lemmas, runtime_initialize_Init_Data_Rat_Lemmas,
};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Prelude::l_instHAdd___redArg___lam__0;
pub static l_Dyadic_instCommRing___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instCommRing___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instCommRing___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__1_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__2_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__3_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instNatCast___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__4_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_pow as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__5_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__6_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_Dyadic_instCommRing___closed__5_value)
            as *mut leanh::LeanObject],
    };
static mut l_Dyadic_instCommRing___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__6_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__7_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__7_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__8_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__8_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__9_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_ofInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__9_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__10_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instOfNat as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instCommRing___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__10_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__11_value: leanh::LeanCtorObject<6> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Dyadic_instCommRing___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__11_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instCommRing___closed__12_value: leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Dyadic_instCommRing___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Dyadic_instCommRing___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__12_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instCommRing: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instCommRing___closed__12_value) as *mut leanh::LeanObject;
pub unsafe fn l_Dyadic_instCommRing___lam__0(
    mut v_x1_35_: *mut leanh::LeanObject,
    mut v_x2_36_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37_ = l_Dyadic_instNatCast___lam__0(v_x1_35_);
    v___x_38_ = l_Dyadic_mul(v___x_37_, v_x2_36_);
    leanh::lean_dec(v___x_37_);
    return v___x_38_;
}
pub unsafe fn l_Dyadic_instCommRing___lam__1(
    mut v_x1_39_: *mut leanh::LeanObject,
    mut v_x2_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = l_Dyadic_ofInt(v_x1_39_);
    v___x_42_ = l_Dyadic_mul(v___x_41_, v_x2_40_);
    leanh::lean_dec(v___x_41_);
    return v___x_42_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Dyadic_Instances(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Dyadic_Instances(
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
pub unsafe fn initialize_Init_Data_Dyadic_Instances(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Dyadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Dyadic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Dyadic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Dyadic_Instances(builtin);
}