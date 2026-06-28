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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Lean_Grind_instFieldRat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_instFieldRat___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_instFieldRat___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_add as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_instNatCast___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_pow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__6_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__5_value) as *mut LeanObject],
};
static mut l_Lean_Grind_instFieldRat___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__7_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_neg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__8_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_sub as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__9_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_ofInt as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__10_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_inv as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__10_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__11_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_div___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__11_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__12_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_zpow___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__12_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__13_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instHAdd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__12_value) as *mut LeanObject],
};
static mut l_Lean_Grind_instFieldRat___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__13_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__14_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Rat_instOfNat as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_instFieldRat___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__14_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__15_value: LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__14_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instFieldRat___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__15_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__16_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__15_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instFieldRat___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__16_value) as *mut LeanObject;
pub static l_Lean_Grind_instFieldRat___closed__17_value: LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__16_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__10_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__11_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_instFieldRat___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__17_value) as *mut LeanObject;
pub static mut l_Lean_Grind_instFieldRat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instFieldRat___closed__17_value) as *mut LeanObject;
pub unsafe fn l_Lean_Grind_instFieldRat___lam__0(
    mut v_x1_45_: *mut LeanObject,
    mut v_x2_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    v___x_47_ = l_Rat_instNatCast___lam__0(v_x1_45_);
    v___x_48_ = l_Rat_mul(v___x_47_, v_x2_46_);
    lean_dec_ref(v___x_47_);
    return v___x_48_;
}
pub unsafe fn l_Lean_Grind_instFieldRat___lam__1(
    mut v_x1_49_: *mut LeanObject,
    mut v_x2_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    v___x_51_ = l_Rat_ofInt(v_x1_49_);
    v___x_52_ = l_Rat_mul(v___x_51_, v_x2_50_);
    lean_dec_ref(v___x_51_);
    return v___x_52_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_Rat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_Rat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring_Rat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_Rat(builtin);
}
