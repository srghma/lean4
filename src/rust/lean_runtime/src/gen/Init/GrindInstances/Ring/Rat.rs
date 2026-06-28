// Lean compiler output
// Module: Init.GrindInstances.Ring.Rat
// Imports: Init.Grind.Ring.OfScientific Init.Data.Rat.Lemmas Init.Data.Int.DivMod.Lemmas Init.Data.Int.Lemmas
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_add, l_Rat_div___boxed, l_Rat_instNatCast___lam__0, l_Rat_instOfNat, l_Rat_inv,
    l_Rat_mul, l_Rat_mul___boxed, l_Rat_neg, l_Rat_ofInt, l_Rat_pow___boxed, l_Rat_sub,
    l_Rat_zpow___boxed,
};
use crate::r#gen::Init::Data::Rat::Lemmas::{
    initialize_Init_Data_Rat_Lemmas, runtime_initialize_Init_Data_Rat_Lemmas,
};
use crate::r#gen::Init::Grind::Ring::OfScientific::{
    initialize_Init_Grind_Ring_OfScientific, runtime_initialize_Init_Grind_Ring_OfScientific,
};
use crate::r#gen::Init::Prelude::l_instHAdd___redArg___lam__0;
pub static l_Lean_Grind_instFieldRat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instFieldRat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_instFieldRat___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_instNatCast___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__6_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instFieldRat___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__7_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__8_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__9_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_ofInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__10_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_inv as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__11_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__12_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_zpow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__13_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instFieldRat___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__14_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Rat_instOfNat as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instFieldRat___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__15_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
                + 0) as u16,
            other: 6,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__14_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instFieldRat___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__16_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instFieldRat___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__17_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__16_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__10_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_instFieldRat___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Grind_instFieldRat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Grind_instFieldRat___lam__0(
    mut v_x1_45_: *mut crate::leanh::LeanObject,
    mut v_x2_46_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_47_ = l_Rat_instNatCast___lam__0(v_x1_45_);
    v___x_48_ = l_Rat_mul(v___x_47_, v_x2_46_);
    crate::leanh::lean_dec_ref(v___x_47_);
    return v___x_48_;
}
pub unsafe fn l_Lean_Grind_instFieldRat___lam__1(
    mut v_x1_49_: *mut crate::leanh::LeanObject,
    mut v_x2_50_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Rat_ofInt(v_x1_49_);
    v___x_52_ = l_Rat_mul(v___x_51_, v_x2_50_);
    crate::leanh::lean_dec_ref(v___x_51_);
    return v___x_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_Rat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_Rat(
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
pub unsafe fn initialize_Init_GrindInstances_Ring_Rat(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Rat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_Rat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_Rat(builtin);
}
