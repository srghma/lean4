// Lean compiler output
// Module: Lean.Widget
// Imports: Lean.Widget.InteractiveCode Lean.Widget.InteractiveDiagnostic Lean.Widget.InteractiveGoal Lean.Widget.TaggedText Lean.Widget.UserWidget Lean.Widget.Commands
use crate::r#gen::Lean::Widget::Commands::{
    initialize_Lean_Widget_Commands, runtime_initialize_Lean_Widget_Commands,
};
use crate::r#gen::Lean::Widget::InteractiveCode::{
    initialize_Lean_Widget_InteractiveCode, runtime_initialize_Lean_Widget_InteractiveCode,
};
use crate::r#gen::Lean::Widget::InteractiveDiagnostic::{
    initialize_Lean_Widget_InteractiveDiagnostic,
    runtime_initialize_Lean_Widget_InteractiveDiagnostic,
};
use crate::r#gen::Lean::Widget::InteractiveGoal::{
    initialize_Lean_Widget_InteractiveGoal, runtime_initialize_Lean_Widget_InteractiveGoal,
};
use crate::r#gen::Lean::Widget::TaggedText::{
    initialize_Lean_Widget_TaggedText, runtime_initialize_Lean_Widget_TaggedText,
};
use crate::r#gen::Lean::Widget::UserWidget::{
    initialize_Lean_Widget_UserWidget, runtime_initialize_Lean_Widget_UserWidget,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveDiagnostic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_TaggedText(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_InteractiveCode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_InteractiveDiagnostic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_InteractiveGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_TaggedText(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Widget_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Widget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Widget(builtin);
}
