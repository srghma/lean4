// Lean compiler output
// Module: Lean.Modifiers
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_TagDeclarationExtension_isTagged,
    l_Lean_TagDeclarationExtension_tag, l_Lean_mkTagDeclarationExtension,
    runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_mainModule;
use crate::r#gen::Lean::PrivateName::{l_Lean_mkPrivateNameCore, l_Lean_privateToUserName};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_ctor_get, lean_dec_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
};
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 69, 120, 116, 0]};
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut LeanObject,14813822476301250067 as *mut LeanObject] };
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    v___x_40_ = l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_;
    v___x_41_ = lean_box(2);
    v___x_42_ = l_Lean_mkTagDeclarationExtension(v___x_40_, v___x_41_);
    return v___x_42_;
}
pub unsafe fn l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2____boxed(
    mut v_a_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_44_: *mut LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
    return v_res_44_;
}
pub unsafe fn l_Lean_addProtected(
    mut v_env_45_: *mut LeanObject,
    mut v_n_46_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
    v___x_47_ = l_Lean_protectedExt;
    v___x_48_ = l_Lean_TagDeclarationExtension_tag(v___x_47_, v_env_45_, v_n_46_);
    return v___x_48_;
}
pub unsafe fn l_Lean_isProtected(
    mut v_env_49_: *mut LeanObject,
    mut v_n_50_: *mut LeanObject,
) -> u8 {
    let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_52_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: u8 = 0;
    v___x_51_ = l_Lean_protectedExt;
    v_toEnvExtension_52_ = lean_ctor_get(v___x_51_, 0);
    v_asyncMode_53_ = lean_ctor_get(v_toEnvExtension_52_, 2);
    v___x_54_ =
        l_Lean_TagDeclarationExtension_isTagged(v___x_51_, v_env_49_, v_n_50_, v_asyncMode_53_);
    return v___x_54_;
}
pub unsafe fn l_Lean_isProtected___boxed(
    mut v_env_55_: *mut LeanObject,
    mut v_n_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_57_: u8 = 0;
    let mut v_r_58_: *mut LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Lean_isProtected(v_env_55_, v_n_56_);
    v_r_58_ = lean_box((v_res_57_) as usize);
    return v_r_58_;
}
pub unsafe fn l_Lean_mkPrivateName(
    mut v_env_59_: *mut LeanObject,
    mut v_n_60_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
    v___x_61_ = l_Lean_Environment_mainModule(v_env_59_);
    v___x_62_ = l_Lean_privateToUserName(v_n_60_);
    v___x_63_ = l_Lean_mkPrivateNameCore(v___x_61_, v___x_62_);
    return v___x_63_;
}
pub unsafe fn l_Lean_mkPrivateName___boxed(
    mut v_env_64_: *mut LeanObject,
    mut v_n_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_66_: *mut LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Lean_mkPrivateName(v_env_64_, v_n_65_);
    lean_dec_ref(v_env_64_);
    return v_res_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Modifiers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_protectedExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_protectedExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Modifiers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Modifiers(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Modifiers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Modifiers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Modifiers(builtin);
}
