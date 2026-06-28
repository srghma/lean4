// Lean compiler output
// Module: Init.GrindInstances.Ring.Int
// Imports: Init.Grind.Ring.Basic Init.Data.Int.Lemmas Init.Data.Int.Pow Init.Data.Int.DivMod.Lemmas Init.Meta
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_mul___boxed, l_Int_neg___boxed, l_Int_ofNat___boxed,
    l_Int_pow___boxed, l_Int_sub___boxed, l_instIntCastInt___lam__0___boxed, l_instOfNat,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Grind::Ring::Basic::{
    initialize_Init_Grind_Ring_Basic, runtime_initialize_Init_Grind_Ring_Basic,
};
use crate::r#gen::Init::Meta::{initialize_Init_Meta, runtime_initialize_Init_Meta};
use crate::r#gen::Init::Prelude::{
    l_instHAdd___redArg___lam__0, l_instPowNat___redArg___lam__0, l_instSMulOfMul___redArg___lam__0,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_mul, lean_nat_to_int};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once,
};
pub static l_Lean_Grind_instCommRingInt___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Grind_instCommRingInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__4_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instPowNat___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__5_value: LeanClosureObject<1> =
    LeanClosureObject {
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
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__4_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_neg___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__7_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__8_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instIntCastInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__9_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instSMulOfMul___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_instCommRingInt___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__9_value) as *mut LeanObject;
pub static l_Lean_Grind_instCommRingInt___closed__10_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instOfNat as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_instCommRingInt___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_instCommRingInt___closed__10_value) as *mut LeanObject;
static mut l_Lean_Grind_instCommRingInt___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_instCommRingInt___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_instCommRingInt___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_instCommRingInt___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Grind_instCommRingInt: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_instCommRingInt___lam__0(
    mut v_x1_36_: *mut LeanObject,
    mut v_x2_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    v___x_38_ = lean_nat_to_int(v_x1_36_);
    v___x_39_ = lean_int_mul(v___x_38_, v_x2_37_);
    lean_dec(v___x_38_);
    return v___x_39_;
}
pub unsafe fn l_Lean_Grind_instCommRingInt___lam__0___boxed(
    mut v_x1_40_: *mut LeanObject,
    mut v_x2_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_42_: *mut LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Lean_Grind_instCommRingInt___lam__0(v_x1_40_, v_x2_41_);
    lean_dec(v_x2_41_);
    return v_res_42_;
}
pub unsafe fn _init_l_Lean_Grind_instCommRingInt___closed__11() -> *mut LeanObject {
    let mut v___f_57_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_58_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_59_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_60_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
    v___f_57_ = l_Lean_Grind_instCommRingInt___closed__5;
    v___f_58_ = l_Lean_Grind_instCommRingInt___closed__0;
    v___x_59_ = l_Lean_Grind_instCommRingInt___closed__10;
    v___f_60_ = lean_alloc_closure(l_Int_ofNat___boxed as *mut core::ffi::c_void, 1, 0);
    v___x_61_ = l_Lean_Grind_instCommRingInt___closed__2;
    v___x_62_ = l_Lean_Grind_instCommRingInt___closed__1;
    v___x_63_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_63_, 0, v___x_62_);
    lean_ctor_set(v___x_63_, 1, v___x_61_);
    lean_ctor_set(v___x_63_, 2, v___f_60_);
    lean_ctor_set(v___x_63_, 3, v___x_59_);
    lean_ctor_set(v___x_63_, 4, v___f_58_);
    lean_ctor_set(v___x_63_, 5, v___f_57_);
    return v___x_63_;
}
pub unsafe fn _init_l_Lean_Grind_instCommRingInt___closed__12() -> *mut LeanObject {
    let mut v___f_64_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_65_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_67_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    v___f_64_ = l_Lean_Grind_instCommRingInt___closed__9;
    v___f_65_ = l_Lean_Grind_instCommRingInt___closed__8;
    v___x_66_ = l_Lean_Grind_instCommRingInt___closed__7;
    v___x_67_ = l_Lean_Grind_instCommRingInt___closed__6;
    v___x_68_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instCommRingInt___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Grind_instCommRingInt___closed__11_once),
        _init_l_Lean_Grind_instCommRingInt___closed__11,
    );
    v___x_69_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_69_, 0, v___x_68_);
    lean_ctor_set(v___x_69_, 1, v___x_67_);
    lean_ctor_set(v___x_69_, 2, v___x_66_);
    lean_ctor_set(v___x_69_, 3, v___f_65_);
    lean_ctor_set(v___x_69_, 4, v___f_64_);
    return v___x_69_;
}
pub unsafe fn _init_l_Lean_Grind_instCommRingInt() -> *mut LeanObject {
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    v___x_70_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_instCommRingInt___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Grind_instCommRingInt___closed__12_once),
        _init_l_Lean_Grind_instCommRingInt___closed__12,
    );
    return v___x_70_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_GrindInstances_Ring_Int(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Grind_instCommRingInt = _init_l_Lean_Grind_instCommRingInt();
    lean_mark_persistent(l_Lean_Grind_instCommRingInt);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_GrindInstances_Ring_Int(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_GrindInstances_Ring_Int(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_GrindInstances_Ring_Int(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_GrindInstances_Ring_Int(builtin);
}
