// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Substructure::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(builtin);
}
