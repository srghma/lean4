// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Reverse
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Data.Nat.Order Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
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
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___redArg(
    mut v_aig_40_: *mut leanh::LeanObject,
    mut v_s_41_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_42_ = l_Array_reverse___redArg(v_s_41_);
    v___x_43_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_43_, 0, v_aig_40_);
    leanh::lean_ctor_set(v___x_43_, 1, v___x_42_);
    return v___x_43_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
    mut v_00_u03b1_44_: *mut leanh::LeanObject,
    mut v_inst_45_: *mut leanh::LeanObject,
    mut v_inst_46_: *mut leanh::LeanObject,
    mut v_w_47_: *mut leanh::LeanObject,
    mut v_aig_48_: *mut leanh::LeanObject,
    mut v_s_49_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___redArg(v_aig_48_, v_s_49_);
    return v___x_50_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___boxed(
    mut v_00_u03b1_51_: *mut leanh::LeanObject,
    mut v_inst_52_: *mut leanh::LeanObject,
    mut v_inst_53_: *mut leanh::LeanObject,
    mut v_w_54_: *mut leanh::LeanObject,
    mut v_aig_55_: *mut leanh::LeanObject,
    mut v_s_56_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_57_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
        v_00_u03b1_51_,
        v_inst_52_,
        v_inst_53_,
        v_w_54_,
        v_aig_55_,
        v_s_56_,
    );
    leanh::lean_dec(v_w_54_);
    leanh::lean_dec_ref(v_inst_53_);
    leanh::lean_dec_ref(v_inst_52_);
    return v_res_57_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___redArg(
    mut v_s_58_: *mut leanh::LeanObject,
    mut v_h__1_59_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = leanh::lean_apply_2(v_h__1_59_, v_s_58_, leanh::lean_box(0));
    return v___x_60_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(
    mut v_00_u03b1_61_: *mut leanh::LeanObject,
    mut v_inst_62_: *mut leanh::LeanObject,
    mut v_inst_63_: *mut leanh::LeanObject,
    mut v_w_64_: *mut leanh::LeanObject,
    mut v_aig_65_: *mut leanh::LeanObject,
    mut v_motive_66_: *mut leanh::LeanObject,
    mut v_s_67_: *mut leanh::LeanObject,
    mut v_h__1_68_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = leanh::lean_apply_2(v_h__1_68_, v_s_67_, leanh::lean_box(0));
    return v___x_69_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___boxed(
    mut v_00_u03b1_70_: *mut leanh::LeanObject,
    mut v_inst_71_: *mut leanh::LeanObject,
    mut v_inst_72_: *mut leanh::LeanObject,
    mut v_w_73_: *mut leanh::LeanObject,
    mut v_aig_74_: *mut leanh::LeanObject,
    mut v_motive_75_: *mut leanh::LeanObject,
    mut v_s_76_: *mut leanh::LeanObject,
    mut v_h__1_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(v_00_u03b1_70_, v_inst_71_, v_inst_72_, v_w_73_, v_aig_74_, v_motive_75_, v_s_76_, v_h__1_77_);
    leanh::lean_dec_ref(v_aig_74_);
    leanh::lean_dec(v_w_73_);
    leanh::lean_dec_ref(v_inst_72_);
    leanh::lean_dec_ref(v_inst_71_);
    return v_res_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(builtin);
}