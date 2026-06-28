// Lean compiler output
// Module: Lean.Compiler.NoncomputableAttr
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_TagDeclarationExtension_isTagged,
    l_Lean_TagDeclarationExtension_tag, l_Lean_mkTagDeclarationExtension,
    runtime_initialize_Lean_EnvExtension,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
};
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut LeanObject,2392490366614390687 as *mut LeanObject] };
static mut l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    v___x_32_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_;
    v___x_33_ = lean_box(0);
    v___x_34_ = l_Lean_mkTagDeclarationExtension(v___x_32_, v___x_33_);
    return v___x_34_;
}
pub unsafe fn l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2____boxed(
    mut v_a_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_36_: *mut LeanObject = core::ptr::null_mut();
    v_res_36_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
    return v_res_36_;
}
pub unsafe fn l_Lean_addNoncomputable(
    mut v_env_37_: *mut LeanObject,
    mut v_declName_38_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
    v___x_39_ = l_Lean_noncomputableExt;
    v___x_40_ = l_Lean_TagDeclarationExtension_tag(v___x_39_, v_env_37_, v_declName_38_);
    return v___x_40_;
}
pub unsafe fn l_Lean_isNoncomputable(
    mut v_env_41_: *mut LeanObject,
    mut v_declName_42_: *mut LeanObject,
    mut v_asyncMode_43_: *mut LeanObject,
) -> u8 {
    let mut v___x_44_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_env_46_: *mut LeanObject,
    mut v_declName_47_: *mut LeanObject,
    mut v_asyncMode_48_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_49_: u8 = 0;
    let mut v_r_50_: *mut LeanObject = core::ptr::null_mut();
    v_res_49_ = l_Lean_isNoncomputable(v_env_46_, v_declName_47_, v_asyncMode_48_);
    lean_dec(v_asyncMode_48_);
    v_r_50_ = lean_box((v_res_49_) as usize);
    return v_r_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_noncomputableExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_noncomputableExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_NoncomputableAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_NoncomputableAttr(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_NoncomputableAttr(builtin);
}
