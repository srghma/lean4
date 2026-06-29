// Lean compiler output
// Module: Lean.Compiler.NoncomputableAttr
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_TagDeclarationExtension_isTagged,
    l_Lean_TagDeclarationExtension_tag, l_Lean_mkTagDeclarationExtension,
    runtime_initialize_Lean_EnvExtension,
};
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2392490366614390687 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_noncomputableExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_32_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_;
    v___x_33_ = crate::leanh::lean_box(0);
    v___x_34_ = l_Lean_mkTagDeclarationExtension(v___x_32_, v___x_33_);
    return v___x_34_;
}
pub unsafe fn l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2____boxed(
    mut v_a_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_36_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
    return v_res_36_;
}
pub unsafe fn l_Lean_addNoncomputable(
    mut v_env_37_: *mut crate::leanh::LeanObject,
    mut v_declName_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_39_ = l_Lean_noncomputableExt;
    v___x_40_ = l_Lean_TagDeclarationExtension_tag(v___x_39_, v_env_37_, v_declName_38_);
    return v___x_40_;
}
pub unsafe fn l_Lean_isNoncomputable(
    mut v_env_41_: *mut crate::leanh::LeanObject,
    mut v_declName_42_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_43_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_45_: u8 = 0;
    v___x_44_ = l_Lean_noncomputableExt;
    v___x_45_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_44_,
        v_env_41_,
        v_declName_42_,
        v_asyncMode_43_,
    );
    return v___x_45_;
}
pub unsafe fn l_Lean_isNoncomputable___boxed(
    mut v_env_46_: *mut crate::leanh::LeanObject,
    mut v_declName_47_: *mut crate::leanh::LeanObject,
    mut v_asyncMode_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_49_: u8 = 0;
    let mut v_r_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_49_ = l_Lean_isNoncomputable(v_env_46_, v_declName_47_, v_asyncMode_48_);
    crate::leanh::lean_dec(v_asyncMode_48_);
    v_r_50_ = crate::leanh::lean_box((v_res_49_) as usize);
    return v_r_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_NoncomputableAttr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_noncomputableExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_noncomputableExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_NoncomputableAttr(
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
pub unsafe fn initialize_Lean_Compiler_NoncomputableAttr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_NoncomputableAttr(builtin);
}
