// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD
// Imports: Std.Sat.AIG.RefVec
use crate::r#gen::Std::Sat::AIG::RefVec::{
    initialize_Std_Sat_AIG_RefVec, runtime_initialize_Std_Sat_AIG_RefVec,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_nat_dec_eq, lean_nat_dec_lt,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(
    mut v_target_31_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_w_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_33_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: u8 = 0;
    v_w_32_ = crate::leanh::lean_ctor_get(v_target_31_, 0);
    v_vec_33_ = crate::leanh::lean_ctor_get(v_target_31_, 1);
    v_idx_34_ = crate::leanh::lean_ctor_get(v_target_31_, 2);
    v___x_35_ = lean_nat_dec_lt(v_idx_34_, v_w_32_);
    if v___x_35_ == 0 {
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_36_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_37_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_37_, 0, v___x_36_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_37_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_35_,
        );
        return v___x_37_;
    } else {
        let mut v_ref_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_43_: u8 = 0;
        v_ref_38_ = lean_array_fget_borrowed(v_vec_33_, v_idx_34_);
        v___x_39_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_40_ = lean_nat_shiftr(v_ref_38_, v___x_39_);
        v___x_41_ = lean_nat_land(v___x_39_, v_ref_38_);
        v___x_42_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_43_ = lean_nat_dec_eq(v___x_41_, v___x_42_);
        crate::leanh::lean_dec(v___x_41_);
        if v___x_43_ == 0 {
            let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_44_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_44_, 0, v___x_40_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_44_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_35_,
            );
            return v___x_44_;
        } else {
            let mut v___x_45_: u8 = 0;
            let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_45_ = 0;
            v___x_46_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_46_, 0, v___x_40_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_46_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_45_,
            );
            return v___x_46_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg___boxed(
    mut v_target_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(v_target_47_);
    crate::leanh::lean_dec_ref(v_target_47_);
    return v_res_48_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD(
    mut v_00_u03b1_49_: *mut crate::leanh::LeanObject,
    mut v_inst_50_: *mut crate::leanh::LeanObject,
    mut v_inst_51_: *mut crate::leanh::LeanObject,
    mut v_aig_52_: *mut crate::leanh::LeanObject,
    mut v_target_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_54_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___redArg(v_target_53_);
    return v___x_54_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___boxed(
    mut v_00_u03b1_55_: *mut crate::leanh::LeanObject,
    mut v_inst_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_aig_58_: *mut crate::leanh::LeanObject,
    mut v_target_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_60_ = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD(
        v_00_u03b1_55_,
        v_inst_56_,
        v_inst_57_,
        v_aig_58_,
        v_target_59_,
    );
    crate::leanh::lean_dec_ref(v_target_59_);
    crate::leanh::lean_dec_ref(v_aig_58_);
    crate::leanh::lean_dec_ref(v_inst_57_);
    crate::leanh::lean_dec_ref(v_inst_56_);
    return v_res_60_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_RefVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_RefVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin);
}
