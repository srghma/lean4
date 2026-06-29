// Lean compiler output
// Module: Lean.Elab.Tactic.BoolToPropSimps
// Imports: Lean.Meta.Tactic.Simp.Attr
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::{
    initialize_Lean_Meta_Tactic_Simp_Attr, l_Lean_Meta_registerSimpAttr,
    runtime_initialize_Lean_Meta_Tactic_Simp_Attr,
};
pub static l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [98, 111, 111, 108, 95, 116, 111, 95, 112, 114, 111, 112, 0]};
static mut l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12477978014155889382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<94> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [115, 105, 109, 112, 32, 108, 101, 109, 109, 97, 115, 32, 99, 111, 110, 118, 101, 114, 116, 105, 110, 103, 32, 98, 111, 111, 108, 101, 97, 110, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 105, 110, 32, 116, 101, 114, 109, 115, 32, 111, 102, 32, 96, 100, 101, 99, 105, 100, 101, 96, 32, 105, 110, 116, 111, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_bool__to__prop: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_18_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16_ = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
    v___x_17_ = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_;
    v___x_18_ = l_Lean_Meta_registerSimpAttr(v___x_16_, v___x_17_, v___x_16_);
    return v___x_18_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2____boxed(
    mut v_a_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_20_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_20_ = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
    return v_res_20_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_bool__to__prop = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_bool__to__prop);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BoolToPropSimps(
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
pub unsafe fn initialize_Lean_Elab_Tactic_BoolToPropSimps(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
}
