// Lean compiler output
// Module: Init.System.Platform
// Imports: Init.Data.Nat.Div.Basic Init.SimpLemmas Init.Data.Nat.Basic Init.Data.String.Bootstrap
use crate::r#gen::Init::Data::Nat::Basic::{
    initialize_Init_Data_Nat_Basic, runtime_initialize_Init_Data_Nat_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::String::Bootstrap::{
    initialize_Init_Data_String_Bootstrap, runtime_initialize_Init_Data_String_Bootstrap,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once, lean_uint8_once,
};
static mut l_System_Platform_isWindows___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Platform_isWindows___closed__0: u8 = 0;
pub static mut l_System_Platform_isWindows: u8 = 0;
static mut l_System_Platform_isOSX___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Platform_isOSX___closed__0: u8 = 0;
pub static mut l_System_Platform_isOSX: u8 = 0;
static mut l_System_Platform_isEmscripten___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Platform_isEmscripten___closed__0: u8 = 0;
pub static mut l_System_Platform_isEmscripten: u8 = 0;
static mut l_System_Platform_target___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_System_Platform_target___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_System_Platform_target: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_System_Platform_getIsWindows___boxed(
    mut v_a_00___x40___internal___hyg_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_30_: u8 = 0;
    let mut v_r_31_: *mut LeanObject = core::ptr::null_mut();
    v_res_30_ = lean_system_platform_windows(v_a_00___x40___internal___hyg_29_);
    v_r_31_ = lean_box((v_res_30_) as usize);
    return v_r_31_;
}
pub unsafe fn l_System_Platform_getIsOSX___boxed(
    mut v_a_00___x40___internal___hyg_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_34_: u8 = 0;
    let mut v_r_35_: *mut LeanObject = core::ptr::null_mut();
    v_res_34_ = lean_system_platform_osx(v_a_00___x40___internal___hyg_33_);
    v_r_35_ = lean_box((v_res_34_) as usize);
    return v_r_35_;
}
pub unsafe fn l_System_Platform_getIsEmscripten___boxed(
    mut v_a_00___x40___internal___hyg_37_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_38_: u8 = 0;
    let mut v_r_39_: *mut LeanObject = core::ptr::null_mut();
    v_res_38_ = lean_system_platform_emscripten(v_a_00___x40___internal___hyg_37_);
    v_r_39_ = lean_box((v_res_38_) as usize);
    return v_r_39_;
}
pub unsafe fn _init_l_System_Platform_isWindows___closed__0() -> u8 {
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41_: u8 = 0;
    v___x_40_ = lean_box(0);
    v___x_41_ = lean_system_platform_windows(v___x_40_);
    return v___x_41_;
}
pub unsafe fn _init_l_System_Platform_isWindows() -> u8 {
    let mut v___x_42_: u8 = 0;
    v___x_42_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_System_Platform_isWindows___closed__0),
        core::ptr::addr_of_mut!(l_System_Platform_isWindows___closed__0_once),
        _init_l_System_Platform_isWindows___closed__0,
    );
    return v___x_42_;
}
pub unsafe fn _init_l_System_Platform_isOSX___closed__0() -> u8 {
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_44_: u8 = 0;
    v___x_43_ = lean_box(0);
    v___x_44_ = lean_system_platform_osx(v___x_43_);
    return v___x_44_;
}
pub unsafe fn _init_l_System_Platform_isOSX() -> u8 {
    let mut v___x_45_: u8 = 0;
    v___x_45_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_System_Platform_isOSX___closed__0),
        core::ptr::addr_of_mut!(l_System_Platform_isOSX___closed__0_once),
        _init_l_System_Platform_isOSX___closed__0,
    );
    return v___x_45_;
}
pub unsafe fn _init_l_System_Platform_isEmscripten___closed__0() -> u8 {
    let mut v___x_46_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_47_: u8 = 0;
    v___x_46_ = lean_box(0);
    v___x_47_ = lean_system_platform_emscripten(v___x_46_);
    return v___x_47_;
}
pub unsafe fn _init_l_System_Platform_isEmscripten() -> u8 {
    let mut v___x_48_: u8 = 0;
    v___x_48_ = lean_uint8_once(
        core::ptr::addr_of_mut!(l_System_Platform_isEmscripten___closed__0),
        core::ptr::addr_of_mut!(l_System_Platform_isEmscripten___closed__0_once),
        _init_l_System_Platform_isEmscripten___closed__0,
    );
    return v___x_48_;
}
pub unsafe fn l_System_Platform_getTarget___boxed(
    mut v_a_00___x40___internal___hyg_50_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_51_: *mut LeanObject = core::ptr::null_mut();
    v_res_51_ = lean_system_platform_target(v_a_00___x40___internal___hyg_50_);
    return v_res_51_;
}
pub unsafe fn _init_l_System_Platform_target___closed__0() -> *mut LeanObject {
    let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    v___x_52_ = lean_box(0);
    v___x_53_ = lean_system_platform_target(v___x_52_);
    return v___x_53_;
}
pub unsafe fn _init_l_System_Platform_target() -> *mut LeanObject {
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    v___x_54_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_System_Platform_target___closed__0),
        core::ptr::addr_of_mut!(l_System_Platform_target___closed__0_once),
        _init_l_System_Platform_target___closed__0,
    );
    return v___x_54_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_Platform(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_System_Platform_isWindows = _init_l_System_Platform_isWindows();
    l_System_Platform_isOSX = _init_l_System_Platform_isOSX();
    l_System_Platform_isEmscripten = _init_l_System_Platform_isEmscripten();
    l_System_Platform_target = _init_l_System_Platform_target();
    lean_mark_persistent(l_System_Platform_target);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_Platform(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_Platform(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_Platform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_Platform(builtin);
}
