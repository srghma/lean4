// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Data.Nat.Order Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(
    mut v_aig_50_: *mut crate::leanh::LeanObject,
    mut v_target_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_combined_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_52_ = crate::leanh::lean_ctor_get(v_target_51_, 2);
    crate::leanh::lean_inc_ref(v_lhs_52_);
    v_rhs_53_ = crate::leanh::lean_ctor_get(v_target_51_, 3);
    crate::leanh::lean_inc_ref(v_rhs_53_);
    crate::leanh::lean_dec_ref(v_target_51_);
    v_combined_54_ = l_Array_append___redArg(v_rhs_53_, v_lhs_52_);
    crate::leanh::lean_dec_ref(v_lhs_52_);
    v___x_55_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_55_, 0, v_aig_50_);
    crate::leanh::lean_ctor_set(v___x_55_, 1, v_combined_54_);
    return v___x_55_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend(
    mut v_00_u03b1_56_: *mut crate::leanh::LeanObject,
    mut v_inst_57_: *mut crate::leanh::LeanObject,
    mut v_inst_58_: *mut crate::leanh::LeanObject,
    mut v_newWidth_59_: *mut crate::leanh::LeanObject,
    mut v_aig_60_: *mut crate::leanh::LeanObject,
    mut v_target_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_62_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(v_aig_60_, v_target_61_);
    return v___x_62_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___boxed(
    mut v_00_u03b1_63_: *mut crate::leanh::LeanObject,
    mut v_inst_64_: *mut crate::leanh::LeanObject,
    mut v_inst_65_: *mut crate::leanh::LeanObject,
    mut v_newWidth_66_: *mut crate::leanh::LeanObject,
    mut v_aig_67_: *mut crate::leanh::LeanObject,
    mut v_target_68_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend(
        v_00_u03b1_63_,
        v_inst_64_,
        v_inst_65_,
        v_newWidth_66_,
        v_aig_67_,
        v_target_68_,
    );
    crate::leanh::lean_dec(v_newWidth_66_);
    crate::leanh::lean_dec_ref(v_inst_65_);
    crate::leanh::lean_dec_ref(v_inst_64_);
    return v_res_69_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___redArg(
    mut v_target_70_: *mut crate::leanh::LeanObject,
    mut v_h__1_71_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lw_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rw_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lw_72_ = crate::leanh::lean_ctor_get(v_target_70_, 0);
    crate::leanh::lean_inc(v_lw_72_);
    v_rw_73_ = crate::leanh::lean_ctor_get(v_target_70_, 1);
    crate::leanh::lean_inc(v_rw_73_);
    v_lhs_74_ = crate::leanh::lean_ctor_get(v_target_70_, 2);
    crate::leanh::lean_inc_ref(v_lhs_74_);
    v_rhs_75_ = crate::leanh::lean_ctor_get(v_target_70_, 3);
    crate::leanh::lean_inc_ref(v_rhs_75_);
    crate::leanh::lean_dec_ref(v_target_70_);
    v___x_76_ = crate::leanh::lean_apply_5(
        v_h__1_71_,
        v_lw_72_,
        v_rw_73_,
        v_lhs_74_,
        v_rhs_75_,
        crate::leanh::lean_box(0),
    );
    return v___x_76_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter(
    mut v_00_u03b1_77_: *mut crate::leanh::LeanObject,
    mut v_inst_78_: *mut crate::leanh::LeanObject,
    mut v_inst_79_: *mut crate::leanh::LeanObject,
    mut v_newWidth_80_: *mut crate::leanh::LeanObject,
    mut v_aig_81_: *mut crate::leanh::LeanObject,
    mut v_motive_82_: *mut crate::leanh::LeanObject,
    mut v_target_83_: *mut crate::leanh::LeanObject,
    mut v_h__1_84_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lw_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rw_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lw_85_ = crate::leanh::lean_ctor_get(v_target_83_, 0);
    crate::leanh::lean_inc(v_lw_85_);
    v_rw_86_ = crate::leanh::lean_ctor_get(v_target_83_, 1);
    crate::leanh::lean_inc(v_rw_86_);
    v_lhs_87_ = crate::leanh::lean_ctor_get(v_target_83_, 2);
    crate::leanh::lean_inc_ref(v_lhs_87_);
    v_rhs_88_ = crate::leanh::lean_ctor_get(v_target_83_, 3);
    crate::leanh::lean_inc_ref(v_rhs_88_);
    crate::leanh::lean_dec_ref(v_target_83_);
    v___x_89_ = crate::leanh::lean_apply_5(
        v_h__1_84_,
        v_lw_85_,
        v_rw_86_,
        v_lhs_87_,
        v_rhs_88_,
        crate::leanh::lean_box(0),
    );
    return v___x_89_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter___boxed(
    mut v_00_u03b1_90_: *mut crate::leanh::LeanObject,
    mut v_inst_91_: *mut crate::leanh::LeanObject,
    mut v_inst_92_: *mut crate::leanh::LeanObject,
    mut v_newWidth_93_: *mut crate::leanh::LeanObject,
    mut v_aig_94_: *mut crate::leanh::LeanObject,
    mut v_motive_95_: *mut crate::leanh::LeanObject,
    mut v_target_96_: *mut crate::leanh::LeanObject,
    mut v_h__1_97_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_98_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend_match__1_splitter(v_00_u03b1_90_, v_inst_91_, v_inst_92_, v_newWidth_93_, v_aig_94_, v_motive_95_, v_target_96_, v_h__1_97_);
    crate::leanh::lean_dec_ref(v_aig_94_);
    crate::leanh::lean_dec(v_newWidth_93_);
    crate::leanh::lean_dec_ref(v_inst_92_);
    crate::leanh::lean_dec_ref(v_inst_91_);
    return v_res_98_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
}
