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
    mut v_aig_40_: *mut crate::leanh::LeanObject,
    mut v_s_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_42_ = l_Array_reverse___redArg(v_s_41_);
    v___x_43_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_43_, 0, v_aig_40_);
    crate::leanh::lean_ctor_set(v___x_43_, 1, v___x_42_);
    return v___x_43_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
    mut v_00_u03b1_44_: *mut crate::leanh::LeanObject,
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
    mut v_w_47_: *mut crate::leanh::LeanObject,
    mut v_aig_48_: *mut crate::leanh::LeanObject,
    mut v_s_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_50_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___redArg(v_aig_48_, v_s_49_);
    return v___x_50_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___boxed(
    mut v_00_u03b1_51_: *mut crate::leanh::LeanObject,
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_inst_53_: *mut crate::leanh::LeanObject,
    mut v_w_54_: *mut crate::leanh::LeanObject,
    mut v_aig_55_: *mut crate::leanh::LeanObject,
    mut v_s_56_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
        v_00_u03b1_51_,
        v_inst_52_,
        v_inst_53_,
        v_w_54_,
        v_aig_55_,
        v_s_56_,
    );
    crate::leanh::lean_dec(v_w_54_);
    crate::leanh::lean_dec_ref(v_inst_53_);
    crate::leanh::lean_dec_ref(v_inst_52_);
    return v_res_57_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___redArg(
    mut v_s_58_: *mut crate::leanh::LeanObject,
    mut v_h__1_59_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = crate::leanh::lean_apply_2(v_h__1_59_, v_s_58_, crate::leanh::lean_box(0));
    return v___x_60_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(
    mut v_00_u03b1_61_: *mut crate::leanh::LeanObject,
    mut v_inst_62_: *mut crate::leanh::LeanObject,
    mut v_inst_63_: *mut crate::leanh::LeanObject,
    mut v_w_64_: *mut crate::leanh::LeanObject,
    mut v_aig_65_: *mut crate::leanh::LeanObject,
    mut v_motive_66_: *mut crate::leanh::LeanObject,
    mut v_s_67_: *mut crate::leanh::LeanObject,
    mut v_h__1_68_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_69_ = crate::leanh::lean_apply_2(v_h__1_68_, v_s_67_, crate::leanh::lean_box(0));
    return v___x_69_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___boxed(
    mut v_00_u03b1_70_: *mut crate::leanh::LeanObject,
    mut v_inst_71_: *mut crate::leanh::LeanObject,
    mut v_inst_72_: *mut crate::leanh::LeanObject,
    mut v_w_73_: *mut crate::leanh::LeanObject,
    mut v_aig_74_: *mut crate::leanh::LeanObject,
    mut v_motive_75_: *mut crate::leanh::LeanObject,
    mut v_s_76_: *mut crate::leanh::LeanObject,
    mut v_h__1_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(v_00_u03b1_70_, v_inst_71_, v_inst_72_, v_w_73_, v_aig_74_, v_motive_75_, v_s_76_, v_h__1_77_);
    crate::leanh::lean_dec_ref(v_aig_74_);
    crate::leanh::lean_dec(v_w_73_);
    crate::leanh::lean_dec_ref(v_inst_72_);
    crate::leanh::lean_dec_ref(v_inst_71_);
    return v_res_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(builtin);
}
