// Lean compiler output
// Module: Init.SizeOf
// Imports: Init.Notation Init.Tactics
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
pub static l_instSizeOfDefault___closed__0_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_default_sizeOf___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instSizeOfDefault___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSizeOfDefault___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instSizeOfNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instSizeOfNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instSizeOfNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSizeOfNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instSizeOfNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instSizeOfNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_default_sizeOf(
    mut v_00_u03b1_25_: *mut crate::leanh::LeanObject,
    mut v_x_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_27_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_27_;
}
pub unsafe fn l_default_sizeOf___boxed(
    mut v_00_u03b1_28_: *mut crate::leanh::LeanObject,
    mut v_x_29_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_30_ = l_default_sizeOf(v_00_u03b1_28_, v_x_29_);
    crate::leanh::lean_dec(v_x_29_);
    return v_res_30_;
}
pub unsafe fn l_instSizeOfDefault(
    mut v_00_u03b1_32_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33_ = l_instSizeOfDefault___closed__0;
    return v___x_33_;
}
pub unsafe fn l_instSizeOfNat___lam__0(
    mut v_n_34_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_n_34_);
    return v_n_34_;
}
pub unsafe fn l_instSizeOfNat___lam__0___boxed(
    mut v_n_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_36_ = l_instSizeOfNat___lam__0(v_n_35_);
    crate::leanh::lean_dec(v_n_35_);
    return v_res_36_;
}
pub unsafe fn l_instSizeOfForallUnit___redArg___lam__0(
    mut v_inst_39_: *mut crate::leanh::LeanObject,
    mut v_f_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = crate::leanh::lean_box(0);
    v___x_42_ = crate::leanh::lean_apply_1(v_f_40_, v___x_41_);
    v___x_43_ = crate::leanh::lean_apply_1(v_inst_39_, v___x_42_);
    return v___x_43_;
}
pub unsafe fn l_instSizeOfForallUnit___redArg(
    mut v_inst_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_45_ = crate::leanh::lean_alloc_closure(
        l_instSizeOfForallUnit___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_45_, 0, v_inst_44_);
    return v___f_45_;
}
pub unsafe fn l_instSizeOfForallUnit(
    mut v_00_u03b1_46_: *mut crate::leanh::LeanObject,
    mut v_inst_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_48_ = crate::leanh::lean_alloc_closure(
        l_instSizeOfForallUnit___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_48_, 0, v_inst_47_);
    return v___f_48_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_SizeOf(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_SizeOf(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_SizeOf(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_SizeOf(builtin);
}
