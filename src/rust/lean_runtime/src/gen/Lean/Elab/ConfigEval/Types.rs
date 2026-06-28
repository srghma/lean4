// Lean compiler output
// Module: Lean.Elab.ConfigEval.Types
// Imports: Lean.Elab.Term.TermElabM Lean.Parser.Term
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    initialize_Lean_Elab_Term_TermElabM, runtime_initialize_Lean_Elab_Term_TermElabM,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_registerInternalExceptionId;
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec_ref, lean_inc, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 110, 102, 105, 103, 69, 118, 97, 108, 0]};
static mut l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__0_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value) as *mut LeanObject,17728754291599005030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__1_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value) as *mut LeanObject,12195177637636718237 as *mut LeanObject] };
static mut l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    v___x_28_ = l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn___closed__2_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_;
    v___x_29_ = l_Lean_registerInternalExceptionId(v___x_28_);
    return v___x_29_;
}
pub unsafe fn l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2____boxed(
    mut v_a_30_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_31_: *mut LeanObject = core::ptr::null_mut();
    v_res_31_ = l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_();
    return v_res_31_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    v___x_32_ = lean_box(0);
    v___x_33_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_34_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_34_, 0, v___x_33_);
    lean_ctor_set(v___x_34_, 1, v___x_32_);
    return v___x_34_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg(
    mut v_inst_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
    v_throw_36_ = lean_ctor_get(v_inst_35_, 0);
    lean_inc(v_throw_36_);
    lean_dec_ref(v_inst_35_);
    v___x_37_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg___closed__0,
    );
    v___x_38_ = lean_apply_2(v_throw_36_, lean_box(0), v___x_37_);
    return v___x_38_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr(
    mut v_m_39_: *mut LeanObject,
    mut v_00_u03b1_40_: *mut LeanObject,
    mut v_inst_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    v___x_42_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___redArg(v_inst_41_);
    return v___x_42_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ConfigEval_Types_0__Lean_Elab_ConfigEval_initFn_00___x40_Lean_Elab_ConfigEval_Types_3111895740____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_ConfigEval_unsupportedExprExceptionId = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Elab_ConfigEval_unsupportedExprExceptionId);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Term_TermElabM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Types(builtin);
}
