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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___redArg(
    mut v_aig_40_: *mut LeanObject,
    mut v_s_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
    v___x_42_ = l_Array_reverse___redArg(v_s_41_);
    v___x_43_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_43_, 0, v_aig_40_);
    lean_ctor_set(v___x_43_, 1, v___x_42_);
    return v___x_43_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
    mut v_00_u03b1_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
    mut v_inst_46_: *mut LeanObject,
    mut v_w_47_: *mut LeanObject,
    mut v_aig_48_: *mut LeanObject,
    mut v_s_49_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
    v___x_50_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___redArg(v_aig_48_, v_s_49_);
    return v___x_50_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse___boxed(
    mut v_00_u03b1_51_: *mut LeanObject,
    mut v_inst_52_: *mut LeanObject,
    mut v_inst_53_: *mut LeanObject,
    mut v_w_54_: *mut LeanObject,
    mut v_aig_55_: *mut LeanObject,
    mut v_s_56_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_57_: *mut LeanObject = core::ptr::null_mut();
    v_res_57_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse(
        v_00_u03b1_51_,
        v_inst_52_,
        v_inst_53_,
        v_w_54_,
        v_aig_55_,
        v_s_56_,
    );
    lean_dec(v_w_54_);
    lean_dec_ref(v_inst_53_);
    lean_dec_ref(v_inst_52_);
    return v_res_57_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___redArg(
    mut v_s_58_: *mut LeanObject,
    mut v_h__1_59_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
    v___x_60_ = lean_apply_2(v_h__1_59_, v_s_58_, lean_box(0));
    return v___x_60_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(
    mut v_00_u03b1_61_: *mut LeanObject,
    mut v_inst_62_: *mut LeanObject,
    mut v_inst_63_: *mut LeanObject,
    mut v_w_64_: *mut LeanObject,
    mut v_aig_65_: *mut LeanObject,
    mut v_motive_66_: *mut LeanObject,
    mut v_s_67_: *mut LeanObject,
    mut v_h__1_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    v___x_69_ = lean_apply_2(v_h__1_68_, v_s_67_, lean_box(0));
    return v___x_69_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter___boxed(
    mut v_00_u03b1_70_: *mut LeanObject,
    mut v_inst_71_: *mut LeanObject,
    mut v_inst_72_: *mut LeanObject,
    mut v_w_73_: *mut LeanObject,
    mut v_aig_74_: *mut LeanObject,
    mut v_motive_75_: *mut LeanObject,
    mut v_s_76_: *mut LeanObject,
    mut v_h__1_77_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_78_: *mut LeanObject = core::ptr::null_mut();
    v_res_78_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastReverse_match__1_splitter(v_00_u03b1_70_, v_inst_71_, v_inst_72_, v_w_73_, v_aig_74_, v_motive_75_, v_s_76_, v_h__1_77_);
    lean_dec_ref(v_aig_74_);
    lean_dec(v_w_73_);
    lean_dec_ref(v_inst_72_);
    lean_dec_ref(v_inst_71_);
    return v_res_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Reverse(builtin);
}
