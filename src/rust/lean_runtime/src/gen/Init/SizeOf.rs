// Lean compiler output
// Module: Init.SizeOf
// Imports: Init.Notation Init.Tactics
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_box, lean_closure_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_unsigned_to_nat,
};
pub static l_instSizeOfDefault___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_default_sizeOf___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_instSizeOfDefault___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSizeOfDefault___closed__0_value) as *mut LeanObject;
pub static l_instSizeOfNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instSizeOfNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSizeOfNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSizeOfNat___closed__0_value) as *mut LeanObject;
pub static mut l_instSizeOfNat: *mut LeanObject =
    core::ptr::addr_of!(l_instSizeOfNat___closed__0_value) as *mut LeanObject;
pub unsafe fn l_default_sizeOf(
    mut v_00_u03b1_25_: *mut LeanObject,
    mut v_x_26_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_27_: *mut LeanObject = core::ptr::null_mut();
    v___x_27_ = lean_unsigned_to_nat(0);
    return v___x_27_;
}
pub unsafe fn l_default_sizeOf___boxed(
    mut v_00_u03b1_28_: *mut LeanObject,
    mut v_x_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_30_: *mut LeanObject = core::ptr::null_mut();
    v_res_30_ = l_default_sizeOf(v_00_u03b1_28_, v_x_29_);
    lean_dec(v_x_29_);
    return v_res_30_;
}
pub unsafe fn l_instSizeOfDefault(mut v_00_u03b1_32_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    v___x_33_ = l_instSizeOfDefault___closed__0;
    return v___x_33_;
}
pub unsafe fn l_instSizeOfNat___lam__0(mut v_n_34_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_n_34_);
    return v_n_34_;
}
pub unsafe fn l_instSizeOfNat___lam__0___boxed(mut v_n_35_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_36_: *mut LeanObject = core::ptr::null_mut();
    v_res_36_ = l_instSizeOfNat___lam__0(v_n_35_);
    lean_dec(v_n_35_);
    return v_res_36_;
}
pub unsafe fn l_instSizeOfForallUnit___redArg___lam__0(
    mut v_inst_39_: *mut LeanObject,
    mut v_f_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    v___x_41_ = lean_box(0);
    v___x_42_ = lean_apply_1(v_f_40_, v___x_41_);
    v___x_43_ = lean_apply_1(v_inst_39_, v___x_42_);
    return v___x_43_;
}
pub unsafe fn l_instSizeOfForallUnit___redArg(mut v_inst_44_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_45_: *mut LeanObject = core::ptr::null_mut();
    v___f_45_ = lean_alloc_closure(
        l_instSizeOfForallUnit___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_45_, 0, v_inst_44_);
    return v___f_45_;
}
pub unsafe fn l_instSizeOfForallUnit(
    mut v_00_u03b1_46_: *mut LeanObject,
    mut v_inst_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_48_: *mut LeanObject = core::ptr::null_mut();
    v___f_48_ = lean_alloc_closure(
        l_instSizeOfForallUnit___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_48_, 0, v_inst_47_);
    return v___f_48_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_SizeOf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_SizeOf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_SizeOf(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_SizeOf(builtin);
}
