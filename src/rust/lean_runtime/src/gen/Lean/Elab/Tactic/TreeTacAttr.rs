// Lean compiler output
// Module: Lean.Elab.Tactic.TreeTacAttr
// Imports: Lean.Meta.Tactic.Simp
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_registerSimpAttr;
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
};
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [73, 110, 116, 101, 114, 110, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 114, 101, 101, 95, 116, 97, 99, 0]};
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject,1742885236933170401 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject,6253359998120991731 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [115, 105, 109, 112, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 117, 115, 101, 100, 32, 98, 121, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 68, 84, 114, 101, 101, 77, 97, 112, 32, 108, 101, 109, 109, 97, 115, 0]};
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 114, 101, 101, 84, 97, 99, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__5_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject,12288741576207087715 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_31_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    v___x_31_ = l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_;
    v___x_32_ = l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_;
    v___x_33_ = l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn___closed__6_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_;
    v___x_34_ = l_Lean_Meta_registerSimpAttr(v___x_31_, v___x_32_, v___x_33_);
    return v___x_34_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2____boxed(
    mut v_a_35_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_36_: *mut LeanObject = core::ptr::null_mut();
    v_res_36_ = l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_();
    return v_res_36_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_TreeTacAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_TreeTacAttr_0__initFn_00___x40_Lean_Elab_Tactic_TreeTacAttr_1721268732____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_treeTacExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_treeTacExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_TreeTacAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_TreeTacAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_TreeTacAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_TreeTacAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_TreeTacAttr(builtin);
}
