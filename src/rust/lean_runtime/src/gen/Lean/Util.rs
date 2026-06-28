// Lean compiler output
// Module: Lean.Util
// Imports: Lean.Util.CollectFVars Lean.Util.CollectLevelParams Lean.Util.CollectMVars Lean.Util.CollectLevelMVars Lean.Util.CollectLooseBVars Lean.Util.FindMVar Lean.Util.FindLevelMVar Lean.Util.MonadCache Lean.Util.PPExt Lean.Util.Path Lean.Util.Profile Lean.Util.RecDepth Lean.Util.ShareCommon Lean.Util.Sorry Lean.Util.Trace Lean.Util.FindExpr Lean.Util.ReplaceExpr Lean.Util.ForEachExpr Lean.Util.ForEachExprWhere Lean.Util.ReplaceLevel Lean.Util.FoldConsts Lean.Util.SCC Lean.Util.TestExtern Lean.Util.OccursCheck Lean.Util.HasConstCache Lean.Util.Heartbeats Lean.Util.SafeExponentiation Lean.Util.NumObjs Lean.Util.NumApps Lean.Util.FVarSubset Lean.Util.SortExprs Lean.Util.Reprove Lean.Util.ParamMinimizer
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, runtime_initialize_Lean_Util_CollectFVars,
};
use crate::r#gen::Lean::Util::CollectLevelMVars::{
    initialize_Lean_Util_CollectLevelMVars, runtime_initialize_Lean_Util_CollectLevelMVars,
};
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, runtime_initialize_Lean_Util_CollectLevelParams,
};
use crate::r#gen::Lean::Util::CollectLooseBVars::{
    initialize_Lean_Util_CollectLooseBVars, runtime_initialize_Lean_Util_CollectLooseBVars,
};
use crate::r#gen::Lean::Util::CollectMVars::{
    initialize_Lean_Util_CollectMVars, runtime_initialize_Lean_Util_CollectMVars,
};
use crate::r#gen::Lean::Util::FVarSubset::{
    initialize_Lean_Util_FVarSubset, runtime_initialize_Lean_Util_FVarSubset,
};
use crate::r#gen::Lean::Util::FindExpr::{
    initialize_Lean_Util_FindExpr, runtime_initialize_Lean_Util_FindExpr,
};
use crate::r#gen::Lean::Util::FindLevelMVar::{
    initialize_Lean_Util_FindLevelMVar, runtime_initialize_Lean_Util_FindLevelMVar,
};
use crate::r#gen::Lean::Util::FindMVar::{
    initialize_Lean_Util_FindMVar, runtime_initialize_Lean_Util_FindMVar,
};
use crate::r#gen::Lean::Util::FoldConsts::{
    initialize_Lean_Util_FoldConsts, runtime_initialize_Lean_Util_FoldConsts,
};
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::r#gen::Lean::Util::ForEachExprWhere::{
    initialize_Lean_Util_ForEachExprWhere, runtime_initialize_Lean_Util_ForEachExprWhere,
};
use crate::r#gen::Lean::Util::HasConstCache::{
    initialize_Lean_Util_HasConstCache, runtime_initialize_Lean_Util_HasConstCache,
};
use crate::r#gen::Lean::Util::Heartbeats::{
    initialize_Lean_Util_Heartbeats, runtime_initialize_Lean_Util_Heartbeats,
};
use crate::r#gen::Lean::Util::MonadCache::{
    initialize_Lean_Util_MonadCache, runtime_initialize_Lean_Util_MonadCache,
};
use crate::r#gen::Lean::Util::NumApps::{
    initialize_Lean_Util_NumApps, runtime_initialize_Lean_Util_NumApps,
};
use crate::r#gen::Lean::Util::NumObjs::{
    initialize_Lean_Util_NumObjs, runtime_initialize_Lean_Util_NumObjs,
};
use crate::r#gen::Lean::Util::OccursCheck::{
    initialize_Lean_Util_OccursCheck, runtime_initialize_Lean_Util_OccursCheck,
};
use crate::r#gen::Lean::Util::PPExt::{
    initialize_Lean_Util_PPExt, runtime_initialize_Lean_Util_PPExt,
};
use crate::r#gen::Lean::Util::ParamMinimizer::{
    initialize_Lean_Util_ParamMinimizer, runtime_initialize_Lean_Util_ParamMinimizer,
};
use crate::r#gen::Lean::Util::Path::{
    initialize_Lean_Util_Path, runtime_initialize_Lean_Util_Path,
};
use crate::r#gen::Lean::Util::Profile::{
    initialize_Lean_Util_Profile, runtime_initialize_Lean_Util_Profile,
};
use crate::r#gen::Lean::Util::RecDepth::{
    initialize_Lean_Util_RecDepth, runtime_initialize_Lean_Util_RecDepth,
};
use crate::r#gen::Lean::Util::ReplaceExpr::{
    initialize_Lean_Util_ReplaceExpr, runtime_initialize_Lean_Util_ReplaceExpr,
};
use crate::r#gen::Lean::Util::ReplaceLevel::{
    initialize_Lean_Util_ReplaceLevel, runtime_initialize_Lean_Util_ReplaceLevel,
};
use crate::r#gen::Lean::Util::Reprove::{
    initialize_Lean_Util_Reprove, runtime_initialize_Lean_Util_Reprove,
};
use crate::r#gen::Lean::Util::SCC::{initialize_Lean_Util_SCC, runtime_initialize_Lean_Util_SCC};
use crate::r#gen::Lean::Util::SafeExponentiation::{
    initialize_Lean_Util_SafeExponentiation, runtime_initialize_Lean_Util_SafeExponentiation,
};
use crate::r#gen::Lean::Util::ShareCommon::{
    initialize_Lean_Util_ShareCommon, runtime_initialize_Lean_Util_ShareCommon,
};
use crate::r#gen::Lean::Util::Sorry::{
    initialize_Lean_Util_Sorry, runtime_initialize_Lean_Util_Sorry,
};
use crate::r#gen::Lean::Util::SortExprs::{
    initialize_Lean_Util_SortExprs, runtime_initialize_Lean_Util_SortExprs,
};
use crate::r#gen::Lean::Util::TestExtern::{
    initialize_Lean_Util_TestExtern, runtime_initialize_Lean_Util_TestExtern,
};
use crate::r#gen::Lean::Util::Trace::{
    initialize_Lean_Util_Trace, runtime_initialize_Lean_Util_Trace,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindLevelMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_MonadCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_PPExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Profile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_RecDepth(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FoldConsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_TestExtern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_OccursCheck(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Heartbeats(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumObjs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumApps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FVarSubset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SortExprs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Reprove(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ParamMinimizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLooseBVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FindMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FindLevelMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_MonadCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_PPExt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Path(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Profile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_RecDepth(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FindExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ReplaceLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FoldConsts(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SCC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_TestExtern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_OccursCheck(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Heartbeats(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SafeExponentiation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_NumObjs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_NumApps(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_FVarSubset(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_SortExprs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Reprove(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ParamMinimizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util(builtin);
}
