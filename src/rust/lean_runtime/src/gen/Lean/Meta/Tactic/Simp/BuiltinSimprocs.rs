// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs
// Imports: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat Lean.Meta.Tactic.Simp.BuiltinSimprocs.Fin Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt Lean.Meta.Tactic.Simp.BuiltinSimprocs.SInt Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char Lean.Meta.Tactic.Simp.BuiltinSimprocs.String Lean.Meta.Tactic.Simp.BuiltinSimprocs.BitVec Lean.Meta.Tactic.Simp.BuiltinSimprocs.List Lean.Meta.Tactic.Simp.BuiltinSimprocs.Array Lean.Meta.Tactic.Simp.BuiltinSimprocs.MethodSpecs Lean.Meta.Tactic.Simp.BuiltinSimprocs.CtorIdx
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Array::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::BitVec::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_BitVec,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_BitVec,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Char::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Core::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::CtorIdx::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Fin::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Int::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::List::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::MethodSpecs::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Nat::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::SInt::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_SInt,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_SInt,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::String::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::UInt::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Fin(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_SInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_BitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_MethodSpecs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin);
}
