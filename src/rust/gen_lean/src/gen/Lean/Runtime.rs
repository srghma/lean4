// Lean compiler output
// Module: Lean.Runtime
// Imports: Init.Prelude
use crate::ffi::{lean_closure_max_args, lean_libuv_version, lean_max_small_nat};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
static mut l_Lean_closureMaxArgs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_closureMaxArgs___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_closureMaxArgs: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_maxSmallNat___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_maxSmallNat___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_maxSmallNat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_libUVVersion___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_libUVVersion___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_libUVVersion: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_closureMaxArgsFn___boxed(
    mut v_a_00___x40___internal___hyg_20_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_21_ = lean_closure_max_args(v_a_00___x40___internal___hyg_20_);
    return v_res_21_;
}
pub unsafe fn l_Lean_maxSmallNatFn___boxed(
    mut v_a_00___x40___internal___hyg_23_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_24_ = lean_max_small_nat(v_a_00___x40___internal___hyg_23_);
    return v_res_24_;
}
pub unsafe fn l_Lean_libUVVersionFn___boxed(
    mut v_a_00___x40___internal___hyg_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_27_ = lean_libuv_version(v_a_00___x40___internal___hyg_26_);
    return v_res_27_;
}
pub unsafe fn _init_l_Lean_closureMaxArgs___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_28_ = crate::leanh::lean_box(0);
    v___x_29_ = lean_closure_max_args(v___x_28_);
    return v___x_29_;
}
pub unsafe fn _init_l_Lean_closureMaxArgs() -> *mut crate::leanh::LeanObject {
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_closureMaxArgs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_closureMaxArgs___closed__0_once),
        _init_l_Lean_closureMaxArgs___closed__0,
    );
    return v___x_30_;
}
pub unsafe fn _init_l_Lean_maxSmallNat___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_31_ = crate::leanh::lean_box(0);
    v___x_32_ = lean_max_small_nat(v___x_31_);
    return v___x_32_;
}
pub unsafe fn _init_l_Lean_maxSmallNat() -> *mut crate::leanh::LeanObject {
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_33_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_maxSmallNat___closed__0),
        core::ptr::addr_of_mut!(l_Lean_maxSmallNat___closed__0_once),
        _init_l_Lean_maxSmallNat___closed__0,
    );
    return v___x_33_;
}
pub unsafe fn _init_l_Lean_libUVVersion___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34_ = crate::leanh::lean_box(0);
    v___x_35_ = lean_libuv_version(v___x_34_);
    return v___x_35_;
}
pub unsafe fn _init_l_Lean_libUVVersion() -> *mut crate::leanh::LeanObject {
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_36_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_libUVVersion___closed__0),
        core::ptr::addr_of_mut!(l_Lean_libUVVersion___closed__0_once),
        _init_l_Lean_libUVVersion___closed__0,
    );
    return v___x_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Runtime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_closureMaxArgs = _init_l_Lean_closureMaxArgs();
    crate::leanh::lean_mark_persistent(l_Lean_closureMaxArgs);
    l_Lean_maxSmallNat = _init_l_Lean_maxSmallNat();
    crate::leanh::lean_mark_persistent(l_Lean_maxSmallNat);
    l_Lean_libUVVersion = _init_l_Lean_libUVVersion();
    crate::leanh::lean_mark_persistent(l_Lean_libUVVersion);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Runtime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Runtime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Runtime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Runtime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Runtime(builtin);
}
