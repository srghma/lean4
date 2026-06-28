// Lean compiler output
// Module: Lean.Elab.Deriving
// Imports: Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util Lean.Elab.Deriving.Inhabited Lean.Elab.Deriving.Nonempty Lean.Elab.Deriving.TypeName Lean.Elab.Deriving.BEq Lean.Elab.Deriving.DecEq Lean.Elab.Deriving.Repr Lean.Elab.Deriving.FromToJson Lean.Elab.Deriving.SizeOf Lean.Elab.Deriving.Hashable Lean.Elab.Deriving.Ord Lean.Elab.Deriving.ToExpr Lean.Elab.Deriving.ReflBEq Lean.Elab.Deriving.LawfulBEq
use crate::r#gen::Lean::Elab::Deriving::BEq::{
    initialize_Lean_Elab_Deriving_BEq, runtime_initialize_Lean_Elab_Deriving_BEq,
};
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Deriving::DecEq::{
    initialize_Lean_Elab_Deriving_DecEq, runtime_initialize_Lean_Elab_Deriving_DecEq,
};
use crate::r#gen::Lean::Elab::Deriving::FromToJson::{
    initialize_Lean_Elab_Deriving_FromToJson, runtime_initialize_Lean_Elab_Deriving_FromToJson,
};
use crate::r#gen::Lean::Elab::Deriving::Hashable::{
    initialize_Lean_Elab_Deriving_Hashable, runtime_initialize_Lean_Elab_Deriving_Hashable,
};
use crate::r#gen::Lean::Elab::Deriving::Inhabited::{
    initialize_Lean_Elab_Deriving_Inhabited, runtime_initialize_Lean_Elab_Deriving_Inhabited,
};
use crate::r#gen::Lean::Elab::Deriving::LawfulBEq::{
    initialize_Lean_Elab_Deriving_LawfulBEq, runtime_initialize_Lean_Elab_Deriving_LawfulBEq,
};
use crate::r#gen::Lean::Elab::Deriving::Nonempty::{
    initialize_Lean_Elab_Deriving_Nonempty, runtime_initialize_Lean_Elab_Deriving_Nonempty,
};
use crate::r#gen::Lean::Elab::Deriving::Ord::{
    initialize_Lean_Elab_Deriving_Ord, runtime_initialize_Lean_Elab_Deriving_Ord,
};
use crate::r#gen::Lean::Elab::Deriving::ReflBEq::{
    initialize_Lean_Elab_Deriving_ReflBEq, runtime_initialize_Lean_Elab_Deriving_ReflBEq,
};
use crate::r#gen::Lean::Elab::Deriving::Repr::{
    initialize_Lean_Elab_Deriving_Repr, runtime_initialize_Lean_Elab_Deriving_Repr,
};
use crate::r#gen::Lean::Elab::Deriving::SizeOf::{
    initialize_Lean_Elab_Deriving_SizeOf, runtime_initialize_Lean_Elab_Deriving_SizeOf,
};
use crate::r#gen::Lean::Elab::Deriving::ToExpr::{
    initialize_Lean_Elab_Deriving_ToExpr, runtime_initialize_Lean_Elab_Deriving_ToExpr,
};
use crate::r#gen::Lean::Elab::Deriving::TypeName::{
    initialize_Lean_Elab_Deriving_TypeName, runtime_initialize_Lean_Elab_Deriving_TypeName,
};
use crate::r#gen::Lean::Elab::Deriving::Util::{
    initialize_Lean_Elab_Deriving_Util, runtime_initialize_Lean_Elab_Deriving_Util,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Inhabited(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Nonempty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_TypeName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_DecEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_FromToJson(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Ord(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_ReflBEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Deriving(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Inhabited(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Nonempty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_TypeName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_DecEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_FromToJson(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Ord(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_ReflBEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving(builtin);
}
