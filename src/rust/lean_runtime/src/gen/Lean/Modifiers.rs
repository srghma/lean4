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
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [112, 114, 111, 116, 101, 99, 116, 101, 100, 69, 120, 116, 0]};
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14813822476301250067 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_40_ = l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_;
    v___x_41_ = crate::leanh::lean_box(2);
    v___x_42_ = l_Lean_mkTagDeclarationExtension(v___x_40_, v___x_41_);
    return v___x_42_;
}
pub unsafe fn l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2____boxed(
    mut v_a_43_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
    return v_res_44_;
}
pub unsafe fn l_Lean_addProtected(
    mut v_env_45_: *mut crate::leanh::LeanObject,
    mut v_n_46_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_47_ = l_Lean_protectedExt;
    v___x_48_ = l_Lean_TagDeclarationExtension_tag(v___x_47_, v_env_45_, v_n_46_);
    return v___x_48_;
}
pub unsafe fn l_Lean_isProtected(
    mut v_env_49_: *mut crate::leanh::LeanObject,
    mut v_n_50_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: u8 = 0;
    v___x_51_ = l_Lean_protectedExt;
    v_toEnvExtension_52_ = crate::leanh::lean_ctor_get(v___x_51_, 0);
    v_asyncMode_53_ = crate::leanh::lean_ctor_get(v_toEnvExtension_52_, 2);
    v___x_54_ =
        l_Lean_TagDeclarationExtension_isTagged(v___x_51_, v_env_49_, v_n_50_, v_asyncMode_53_);
    return v___x_54_;
}
pub unsafe fn l_Lean_isProtected___boxed(
    mut v_env_55_: *mut crate::leanh::LeanObject,
    mut v_n_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_57_: u8 = 0;
    let mut v_r_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Lean_isProtected(v_env_55_, v_n_56_);
    v_r_58_ = crate::leanh::lean_box((v_res_57_) as usize);
    return v_r_58_;
}
pub unsafe fn l_Lean_mkPrivateName(
    mut v_env_59_: *mut crate::leanh::LeanObject,
    mut v_n_60_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_61_ = l_Lean_Environment_mainModule(v_env_59_);
    v___x_62_ = l_Lean_privateToUserName(v_n_60_);
    v___x_63_ = l_Lean_mkPrivateNameCore(v___x_61_, v___x_62_);
    return v___x_63_;
}
pub unsafe fn l_Lean_mkPrivateName___boxed(
    mut v_env_64_: *mut crate::leanh::LeanObject,
    mut v_n_65_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_66_ = l_Lean_mkPrivateName(v_env_64_, v_n_65_);
    crate::leanh::lean_dec_ref(v_env_64_);
    return v_res_66_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Modifiers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_protectedExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_protectedExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Modifiers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Modifiers(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Modifiers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Modifiers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Modifiers(builtin);
}
